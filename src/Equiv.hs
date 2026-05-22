{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE PatternGuards #-}

module Equiv where

import Syntax
import Eval
import Utils

--------------------------------------------------------------------------------

equivK :: GKinds -> Lv -> ValK -> ValK -> Bool
equivK glbK d k k' = case (k, k') of
  (VKAlias gnm _, VKAlias gnm' _) 
    | gnm == gnm' -> True
  _               -> equivBody (unaliasK k) (unaliasK k')
  where equivBody bk bk' =  case (bk, bk') of
          (VKStar             , VKStar               ) -> True
          (VKArr      a  b    , VKArr      a' b'     ) -> equivK glbK d a a' && equivK glbK d b b'
          (VKVar      l       , VKVar      l'        ) -> l == l'
          (VKForall _ body env, VKForall _ body' env') ->
            let vk  = evalK glbK (freshK d : env ) body
                vk' = evalK glbK (freshK d : env') body'
            in equivK glbK (d + 1) vk vk'
          _                                            -> False

--------------------------------------------------------------------------------

equivT :: GTypes -> GKinds -> Lv -> Lv -> ValT -> ValT -> Bool
equivT glbT glbK dT dK v v'
  | VAlias gnm  args  _ <- v ,
    VAlias gnm' args' _ <- v',
    gnm == gnm'              ,
    checkArgs args args' = True
  | otherwise            = equivBody (unaliasT v) (unaliasT v')
  where checkArgs args args' = case (args, args') of
          (Emp         , Emp           ) -> True
          (AppT argsT a, AppT argsT' a') -> equivT glbT glbK dT dK a a' && checkArgs argsT argsT'
          (AppK argsK k, AppK argsK' k') -> equivK glbK dK k k'         && checkArgs argsK argsK'
          _                              -> False

        equivBody bv bv' = case (bv, bv') of
          (VClosure {}, VClosureK{} ) -> False
          (VClosureK{}, VClosure {} ) -> False
          (VClosure {}, _           ) -> etaT
          (_          , VClosure {} ) -> etaT
          (VClosureK{}, _           ) -> etaK
          (_          , VClosureK{} ) -> etaK
          (VNeu     ne, VNeu     ne') -> equivNeu dT dK ne ne'
          _                           -> False
          where vT   = freshT dT
                vK   = freshK dK
                etaT = equivT glbT glbK (dT + 1)  dK      (appT  glbT glbK bv vT) (appT  glbT glbK bv' vT) 
                etaK = equivT glbT glbK  dT      (dK + 1) (appTK glbT glbK bv vK) (appTK glbT glbK bv' vK) 
          
        equivNeu dT' dK' ne ne' = case (ne, ne') of
          (NeuVar    l, NeuVar     l') -> l == l'
          (NeuGlobal g, NeuGlobal  g') -> g == g'
          (NeuConst  c, NeuConst   c') -> equivConstT  dK' c c'
          (NeuApp  f a, NeuApp  f' a') -> equivNeu dT' dK' f f' && equivT glbT glbK dT' dK' a a'
          (NeuAppK f k, NeuAppK f' k') -> equivNeu dT' dK' f f' && equivK      glbK     dK' k k'
          _                            -> False

        equivConstT dK' c c' = case (c, c') of
          (TBase   b, TBase   b') -> b == b'
          (TForall k, TForall k') -> equivK glbK dK' k k'
          (TForallK , TForallK  ) -> True
          _                       -> False
