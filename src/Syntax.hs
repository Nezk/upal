{-# LANGUAGE DerivingVia #-}

module Syntax where

import Data.IORef (IORef)
import Data.Map   (Map)
import Data.Text  (Text)

--------------------------------------------------------------------------------

newtype Ix = Ix { unIx :: Int } deriving (Show, Num, Eq, Ord) via Int
newtype Lv = Lv { unLv :: Int } deriving (Show, Num, Eq, Ord) via Int

newtype UName = UName { unUName :: String } deriving (Show, Eq)      via String 
newtype GName = GName { unGName :: String } deriving (Show, Eq, Ord) via String 
newtype LName = LName { unLName :: String } deriving (Show, Eq)      via String 
newtype HName = HName { unHName :: String } deriving (Show, Eq)      via String 
newtype MName = MName { unMName :: String } deriving (Show, Eq, Ord) via String 

type GKinds  = Map GName ValK
type GTypes  = Map GName ValT
type GErased = Map GName Thunk

type Names = [LName]
type Kinds = [Kind]
type EnvT  = [ValT]

data Pos = Pos String Int Int deriving (Show, Eq)

--------------------------------------------------------------------------------

data Lit
  = LInt    Integer
  | LDouble Double
  | LString Text
  | LUnit

data Const
  = Int | Double | String | Unit | Arr | IO
  deriving Eq

data ConstT k
  = TForall k
  | TForallK                    
  | TBase Const

--------------------------------------------------------------------------------

data RawK
  = RKStar
  | RKArr          RawK RawK
  | RKForall LName RawK
  | RKVar          UName

data RawT     
  = RTVar                        UName
  | RTConst                      Const
  | RTTLam    LName (Maybe RawK) RawT
  | RTTKLam   LName              RawT
  | RTTApp                       RawT  RawT
  | RTKApp                       RawT  RawK
  | RTLet     LName (Maybe RawK) RawT  RawT
  | RTForall  LName (Maybe RawK) RawT
  | RTForallK LName              RawT
  | RTLoc     Pos                RawT

data Raw
  = RVar    UName
  | RConst                     ConstE
  | RLit                       Lit
  | RLam    LName (Maybe RawT) Raw
  | RTLam   LName (Maybe RawK) Raw
  | RKLam   LName              Raw
  | RApp                       Raw Raw
  | RTApp                      Raw RawT
  | RKApp                      Raw RawK
  | RAnn                       Raw RawT
  | RLet    LName (Maybe RawT) Raw Raw  
  | RReturn                    Raw
  | RBind                      Raw Raw
  | RHole   HName (Maybe Raw)
  | RLoc    Pos                Raw

data RawDecl
  = RDeclKind  GName RawK
  | RDeclType  GName RawK RawT
  | RDeclFun   GName RawT Raw
  | RDeclExc         Raw 
  | RDeclEvalT       RawT
  | RDLoc      Pos   RawDecl

data RawModule
  = RModule MName [MName] [RawDecl]

newtype RawProgram
  = RProgram [RawDecl]

--------------------------------------------------------------------------------

data Kind
  = KStar          
  | KArr          Kind Kind
  | KForall LName Kind 
  | KVar          Ix        
  | KGlobal       GName

data Type
  = TVar                Ix                     
  | TConst             (ConstT Kind) 
  | TGlobal             GName                         
  | TLam    LName Kind  Type      
  | TKLam   LName       Type      
  | TLet    LName       Type Type    -- kind annotations aren't used anywhere for term-types, so… not sure about it though
  | TApp                Type Type 
  | TKApp               Type Kind

--------------------------------------------------------------------------------

data ValK
  = VKStar
  | VKArr          ValK ValK
  | VKForall LName Kind EnvK 
  | VKVar          Lv
  | VKAlias  GName ValK

type EnvK   = [ValK]
type TKinds = [ValK]

data Args
  = Emp
  | AppT Args ValT
  | AppK Args ValK

data ValT
  = VNeu                   NeuT
  | VClosure  LName ValK   Type EnvT EnvK
  | VClosureK LName        Type EnvT EnvK
  | VAlias    GName        Args ValT

data NeuT
  = NeuVar     Lv      
  | NeuGlobal  GName
  | NeuConst  (ConstT ValK)
  | NeuApp     NeuT   ValT
  | NeuAppK    NeuT   ValK

--------------------------------------------------------------------------------

data NfT
  = NfNeu               NeuNfT  
  | NfLam  LName Kind   NfT     
  | NfLamK LName        NfT

data NeuNfT
  = NfNeuConst        (ConstT Kind)      
  | NfNeuGlobal GName             
  | NfNeuBVar   Ix                
  | NfNeuApp           NeuNfT NfT 
  | NfNeuKApp          NeuNfT Kind

--------------------------------------------------------------------------------

data Exp
  = EVar    Ix   
  | EGlobal GName

  | EConst  ConstE
  | ELit    Lit

  | ELam  LName Type Exp     
  | ETLam LName Kind Exp     
  | EKLam LName      Exp     
  
  | EApp  Exp Exp                    
  | ETApp Exp Type                   
  | EKApp Exp Kind                   
  
  | ELet LName Type Exp Exp -- TODO: think about necessity of Type annotation in let term 

  | EReturn Exp                      
  | EBind   Exp Exp                  

  | EHole HName (Maybe Exp)          

data ConstE
  = EPutStr   | EGetLine  | EReadFile | EWriteFile 
  | EArgCount | EArgAt
  
  | EAdd  | ESub  | EMul          
  | EAddD | ESubD | EMulD | EDivD 
  | ETrunc
  
  | EIntEq | EDoubleEq | EStringEq 
  
  | EConcat                        
  | ESubstring | ELength | EShowInt | EShowDouble                         

--------------------------------------------------------------------------------

data Erased
  = XVar    Ix     
  | XGlobal GName
  | XConst  ConstE
  | XLit    Lit            
  | XLam    Erased
  | XApp    Erased Erased
  | XLet    Erased Erased
  | XReturn Erased
  | XBind   Erased Erased

type Env      = [Thunk] 
type ArgsE    = [Thunk] 
type ExcDecls = [Exp]   

data ThunkState
  = Unevaluated Erased Env
  | Evaluating
  | Evaluated   ValE

newtype Thunk
  = Thunk (IORef ThunkState)

data ValE
  = VClosureE Erased   Env
  | VLit      Lit
  | VPartial  ConstE   ArgsE
  | VIOAct    ValIOAct

data ValIOAct
  = IOReturn     Thunk
  | IOStandalone IOPrim
  | IOBind       Thunk Thunk

data IOPrim
  = IPutStr    Thunk
  | IGetLine
  | IReadFile  Thunk
  | IWriteFile Thunk Thunk
  | IArgCount
  | IArgAt     Thunk

--------------------------------------------------------------------------------

type Depth = Int
type Views = [View]

data View
  = VwClosure    Erased Views  
  | VwLit        Lit                
  | VwPartial    ConstE Views                  
  | VwIOReturn   View
  | VwIOBind     View   View
  | VwIPutStr    View
  | VwIGetLine   
  | VwIReadFile  View
  | VwIWriteFile View   View
  | VwIArgCount  
  | VwIArgAt     View
  | VwOmitted    
  | VwEvaluating 
  | VwUneval     Erased

--------------------------------------------------------------------------------

data Decl
  = DeclKind  GName Kind
  | DeclType  GName Kind Type
  | DeclFun   GName Type Exp 
  | DeclExc              Exp
  | DeclEvalT       Kind Type
  | DLoc      Pos        Decl

data Module
  = Module MName [MName] [Decl]

newtype Program
  = Program [Decl]
