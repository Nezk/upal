# Upal

A typechecker for [System U](https://en.wikipedia.org/wiki/System_U).

System U is known to be logically inconsistent via Girard's paradox. (Although Girard originally proved this for System U, the implementation of the paradox below is based on Herman Geuvers and Randy Pollack's formalization of Antonius Hurkens' simplified proof for System U⁻).

Because it's inconsistent, we can construct a looping combinator which allows unrestricted recursion. While it has been shown that standard fixed-point combinators (like Church's and Turing's) cannot be typed in System U⁻ (and it's believed to hold for System U as well), the looping combinator has the exact same computational power.

For a detailed analysis of this, see the paper [*On Fixed point and Looping Combinators in Type Theory*](https://www.cs.ru.nl/~herman/PUBS/TLCApaper.pdf) by Herman Geuvers and Joep Verkoelen. 

And here is the looping combinator itself, in all its glory:

```
module loop where

V ∷ ◻
V = ∀ A ∷ ◻. ((A → *) → (A → *)) → A → *

U ∷ ◻
U = V → *

sb ∷ ∀ A ∷ ◻. ((A → *) → (A → *)) → A → U
sb = Λ A. λ r a. λ z. r (z {A} r) a

le ∷ (U → *) → (U → *)
le = λ i. λ u. u (Λ A. λ r a. i (sb {A} r a))

induct ∷ (U → *) → *
induct = λ i. ∀ x ∷ U. le i x → i x

WF ∷ U
WF = λ z. induct (z {U} le)

ω : ∀ a ∷ U → *. induct a → a WF
ω = Λ a. λ y. y [WF] (Λ g. y [sb {U} le g])

I ∷ * → U → *
I = λ B. λ x. (∀ a ∷ U → *. le a x → a (sb {U} le x)) → B

lemma : ∀ B ∷ *. (B → B) → induct (I B)
lemma = Λ B. λ f. Λ _. λ p. λ q.
        f (q [I B] p (Λ a. q [λ d. a (sb {U} le d)]))

lemma2 : ∀ B ∷ *. (B → B) → (∀ i ∷ U → *. induct i → i WF) → B
lemma2 = Λ B. λ f. λ x.
         x [I B] (lemma [B] f) (Λ i. x [λ y. i (sb {U} le y)])

loop : ∀ B ∷ *. (B → B) → B
loop = Λ B. λ f. lemma2 [B] f ω
```

Dumping the erased terms reveals that, once type information is removed, the looping combinator erases to a fixed-point one:

```
$ ./upal --dump examples/loop.ul
Loading module loop


──────── Erased ────────

ω =
  λ. #0 #0

lemma =
  λ. λ. λ. #2 (#0 #1 #0)

lemma2 =
  λ. λ. #0 (lemma #1) #0

loop =
  λ. lemma2 #0 ω

─────────────────────────

Typechecking succeeded.
```

### Features

* `--dump`: Prints the erased, untyped lambda terms defined in the “module”
* `>> e` / `⊢ τ`: Interactive top-level commands: `>> e` executes a term `e` (without running IO side effects), `⊢ τ` normalizes a type `τ` and prints its kind
* `?hole` / `?hole{e}`: Typed holes that display the local context and expected goal, with an optional guess `e`

The evaluation is lazy (call-by-need).

The `Makefile` wraps Cabal: `make` builds the binary, and `make test` runs all examples.

## Language Reference

### Kinds

| Syntax | Description |
| :--- | :--- |
| `*` | Base kind |
| `κ → κ′` | Arrow kind |
| `∀ a ∷ ◻. κ` | Universal quantification over kinds on kind level |

### Types

| Syntax | Description |
| :--- | :--- |
| `Int`, `Double`, `String`, `()` | Base types |
| `IO τ` | IO monad |
| `τ → τ′` | Function type |
| `∀ a ∷ κ. τ` | Universal quantification over types of kind `κ` |
| `∀ a ∷ ◻. τ` | Universal quantification over kinds on type level |
| `λ a ∷ κ. τ` | Type lambda, kind annotation is optional |
| `Λ a ∷ ◻. τ` | Kind lambda, kind annotation is optional |
| `τ σ` | Type application |
| `τ {κ}` | Kind application |

### Terms

| Syntax | Description |
| :--- | :--- |
| `λ x : τ. e` | Lambda, type annotation is optional |
| `Λ a ∷ κ. e` | Type lambda, kind annotation is optional |
| `Λ a ∷ ◻. e` | Kind lambda, kind annotation is optional |
| `e e′` | Term application |
| `e [τ]` | Type application |
| `e {κ}` | Kind application |
| `let x : τ = e in e′` | Let binding, type annotation is optional |
| `return e` | IO monad lift |
| `e >>= e′` | IO monad bind |
| `42`, `3.14`, `"hello"`, `()` | Integer, double, string, and unit literals |
| `(e : τ)` | Type annotation |
| `?h` / `?h{e}` | Typed hole, optionally containing a guess `e` |

### Built-ins

| Syntax | Type |
| :--- | :--- |
| `(+)`, `(-)`, `(*)` | `Int → Int → Int` |
| `(+.)`, `(-.)`, `(*.)` | `Double → Double → Double` |
| `(/.)` | `Double → Double → Option Double` |
| `trunc` | `Double → Int` |
| `(==)` | `Int → Int → Bool` |
| `(=.)` | `Double → Double → Bool` |
| `(=^)` | `String → String → Bool` |
| `(^)` | `String → String → String` |
| `length` | `String → Int` |
| `substring` | `Int → Int → String → String` |
| `showInt` | `Int → String` |
| `showDouble` | `Double → String` |
| `putStr` | `String → IO ()` |
| `getLine` | `IO (Option String)` |
| `readFile` | `String → IO (Result String String)` |
| `writeFile` | `String → String → IO (Result String ())` |
| `argCount` | `IO Int` |
| `argAt` | `Int → IO (Option String)` |

Where `Bool`, `Option` and `Result` are Church-encoded (i. e., they are not built-ins):

* `Bool       = ∀ R ∷ *.      R  →      R →  R`
* `Option A   = ∀ R ∷ *.      R  → (A → R) → R`
* `Result A B = ∀ R ∷ *. (A → R) → (B → R) → R`
