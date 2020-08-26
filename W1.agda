{-# OPTIONS --type-in-type #-}

module W1 where

open import Agda.Primitive using (Level; _⊔_)

record Σ {l₁ l₂ : Level} (τ₁ : Set l₁) (τ₂ : τ₁ → Set l₂) : Set (l₁ ⊔ l₂) where
  constructor _,_
  field
    proj₁ : τ₁
    proj₂ : τ₂ proj₁
open Σ using (proj₁; proj₂) public
infixr 4 _,_
syntax Σ τ₁ (λ v₁ → τ₂) = Σ[ v₁ ∈ τ₁ ] τ₂
infix 2 Σ
infixr 2 _×_
_×_ : {l₁ l₂ : Level} → Set l₁ → Set l₂ → Set (l₁ ⊔ l₂)
τ₁ × τ₂ = Σ τ₁ (λ _ → τ₂)

infixr 5 _∷l_
data List (τ : Set) : Set where
  [l] : List τ
  _∷l_ : τ → List τ → List τ

-- data Place : Set
-- data Corner : Set
-- data Edge : Set
--
-- data Place where
--   PRoot : Place
--   PCorner : Fin 3 → Corner → Place
--   PEdge : Fin 2 → Edge → Place
-- data Corner where
--   CRoot : Fin 4 → Corner
--   CCorner : Fin 2 → Corner → Corner
--   CEdge : Edge → Corner
-- data Edge where
--   ECorner : Fin 3 → Corner → Edge
--   EEdge : Fin 2 → Edge → Edge

-- Root = Place × Corner⁴
-- Corner = Place × Edge × Place × Corner × Edge × Place × Corner × Edge
-- Edge = Place × Edge × Place × Corner × Edge

data Rotation : Set where
  RUp RRight RDown RLeft : Rotation
data CornerCornerDir : Set where
  CCDUp CCDRight : CornerCornerDir
data CornerEdgeDir : Set where
  CEDUp CEDRight CEDDown : CornerEdgeDir
data CornerPlace : Set where
  CP1 CP2 CP3 : CornerPlace
data EdgeEdgeDir : Set where
  EEDUp EEDRight : EdgeEdgeDir
data EdgePlace : Set where
  EP1 EP2 : EdgePlace
data ConnectionPoint : Set where
  CPRoot : ConnectionPoint
  CPPlace : ConnectionPoint
  CPCorner : ConnectionPoint
  CPEdge : ConnectionPoint
data Move : ConnectionPoint → ConnectionPoint → Set where
  MRootPlace : Move CPRoot CPPlace
  MRootCorner : Rotation → Move CPRoot CPCorner
  MCornerPlace : CornerPlace → Move CPCorner CPPlace
  MCornerCorner : CornerCornerDir → Move CPCorner CPCorner
  MCornerEdge : CornerEdgeDir → Move CPCorner CPEdge
  MEdgePlace : EdgePlace → Move CPEdge CPPlace
  MEdgeCorner : Move CPEdge CPCorner
  MEdgeEdge : EdgeEdgeDir → Move CPEdge CPEdge
infixr 5 _∷p_
data Path : ConnectionPoint → ConnectionPoint → Set where
  [p] : {cp : ConnectionPoint} → Path cp cp
  _∷p_ : {cp₁ cp₂ cp₃ : ConnectionPoint} → Move cp₁ cp₂ → Path cp₂ cp₃ → Path cp₁ cp₃
infixl 5 _bp∷_
data BackPath : ConnectionPoint → ConnectionPoint → Set where
  [bp] : {cp : ConnectionPoint} → BackPath cp cp
  _bp∷_ : {cp₁ cp₂ cp₃ : ConnectionPoint} → BackPath cp₁ cp₂ → Move cp₂ cp₃ → BackPath cp₁ cp₃
Place : Set
Place = Rotation × Path CPRoot CPPlace
move-rotation : {cp₁ cp₂ : ConnectionPoint} → Move cp₁ cp₂ → Rotation
move-rotation MRootPlace = RUp
move-rotation (MRootCorner d) = d
move-rotation (MCornerPlace p) = RUp
move-rotation (MCornerCorner CCDUp) = RUp
move-rotation (MCornerCorner CCDRight) = RRight
move-rotation (MCornerEdge CEDUp) = RUp
move-rotation (MCornerEdge CEDRight) = RRight
move-rotation (MCornerEdge CEDDown) = RDown
move-rotation (MEdgePlace p) = RUp
move-rotation MEdgeCorner = RUp
move-rotation (MEdgeEdge EEDUp) = RUp
move-rotation (MEdgeEdge EEDRight) = RRight
infixl 7 _•r_
_•r_ : Rotation → Rotation → Rotation
RUp •r b = b
RRight •r RUp = RRight
RRight •r RRight = RDown
RRight •r RDown = RLeft
RRight •r RLeft = RUp
RDown •r RUp = RDown
RDown •r RRight = RLeft
RDown •r RDown = RUp
RDown •r RLeft = RRight
RLeft •r RUp = RLeft
RLeft •r RRight = RUp
RLeft •r RDown = RRight
RLeft •r RLeft = RDown
infixr 8 _r¯¹
_r¯¹ : Rotation → Rotation
RUp r¯¹ = RUp
RRight r¯¹ = RLeft
RDown r¯¹ = RDown
RLeft r¯¹ = RRight
path-rotation : {cp₁ cp₂ : ConnectionPoint} → Path cp₁ cp₂ → Rotation
path-rotation [p] = RUp
path-rotation (m ∷p p) = move-rotation m •r path-rotation p
path-snoc : {cp₁ cp₂ cp₃ : ConnectionPoint} → Path cp₁ cp₂ → Move cp₂ cp₃ → Path cp₁ cp₃
path-snoc [p] m = _∷p_ m [p]
path-snoc (m' ∷p p) m = m' ∷p path-snoc p m
backpath-cons : {cp₁ cp₂ cp₃ : ConnectionPoint} → Move cp₁ cp₂ → BackPath cp₂ cp₃ → BackPath cp₁ cp₃
backpath-cons {cp₁} m [bp] = [bp] bp∷ m
backpath-cons m (bp bp∷ m') = backpath-cons m bp bp∷ m'
backpath : {cp₁ cp₂ : ConnectionPoint} → Path cp₁ cp₂ → BackPath cp₁ cp₂
backpath {cp₁} [p] = [bp]
backpath (_∷p_ m p) = backpath-cons m (backpath p)
fwd-path : {cp₁ cp₂ : ConnectionPoint} → BackPath cp₁ cp₂ → Path cp₁ cp₂
fwd-path [bp] = [p]
fwd-path (bp bp∷ m) = path-snoc (fwd-path bp) m
origin-place : {cp₁ cp₂ : ConnectionPoint} → Move cp₁ cp₂ → Rotation × Move cp₁ CPPlace
origin-place MRootPlace = RUp , MRootPlace
origin-place (MRootCorner d) = d , MRootPlace
origin-place (MCornerPlace i) = RUp , MCornerPlace i
origin-place (MCornerCorner CCDUp) = RUp , MCornerPlace CP2
origin-place (MCornerCorner CCDRight) = RRight , MCornerPlace CP3
origin-place (MCornerEdge CEDUp) = RUp , MCornerPlace CP1
origin-place (MCornerEdge CEDRight) = RRight , MCornerPlace CP2
origin-place (MCornerEdge CEDDown) = RDown , MCornerPlace CP3
origin-place (MEdgePlace i) = RUp , MEdgePlace i
origin-place MEdgeCorner = RUp , MEdgePlace EP2
origin-place (MEdgeEdge EEDUp) = RUp , MEdgePlace EP1
origin-place (MEdgeEdge EEDRight) = RRight , MEdgePlace EP2

-- rightmost edge of next left node
move-help1 : BackPath CPRoot CPEdge → Rotation × BackPath CPRoot CPEdge
move-help1 ([bp] bp∷ MRootCorner d bp∷ MCornerEdge CEDUp) =
  RLeft , [bp] bp∷ MRootCorner (RLeft •r d) bp∷ MCornerEdge CEDDown bp∷ MEdgeEdge EEDRight
move-help1 (bp bp∷ MCornerCorner CCDUp bp∷ MCornerEdge CEDUp) =
  RLeft , bp bp∷ MCornerEdge CEDUp bp∷ MEdgeEdge EEDRight bp∷ MEdgeEdge EEDRight
move-help1 (bp bp∷ MCornerCorner CCDRight bp∷ MCornerEdge CEDUp) =
  RLeft , bp bp∷ MCornerEdge CEDRight bp∷ MEdgeEdge EEDRight bp∷ MEdgeEdge EEDRight
move-help1 (bp bp∷ MEdgeCorner bp∷ MCornerEdge CEDUp) =
  RLeft , bp bp∷ MEdgeEdge EEDUp bp∷ MEdgeEdge EEDRight bp∷ MEdgeEdge EEDRight
move-help1 (bp bp∷ MCornerEdge CEDRight) =
  RDown , bp bp∷ MCornerCorner CCDUp bp∷ MCornerEdge CEDDown
move-help1 (bp bp∷ MCornerEdge CEDDown) =
  RDown , bp bp∷ MCornerCorner CCDRight bp∷ MCornerEdge CEDDown
move-help1 (bp bp∷ MEdgeEdge EEDUp) =
  let d , bp' = move-help1 bp in
  {!   !} , bp' bp∷ MEdgeEdge EEDUp
move-help1 (bp bp∷ MEdgeEdge EEDRight) =
  RDown , bp bp∷ MEdgeCorner bp∷ MCornerEdge CEDDown bp∷ MEdgeEdge EEDRight

-- leftmost edge of next right node
move-help2 : BackPath CPRoot CPEdge → Rotation × BackPath CPRoot CPEdge
move-help2 (bp bp∷ MCornerEdge CEDUp) =
  RRight , bp bp∷ MCornerCorner CCDUp bp∷ MCornerEdge CEDUp
move-help2 (bp bp∷ MCornerEdge CEDRight) =
  RRight , bp bp∷ MCornerCorner CCDRight bp∷ MCornerEdge CEDUp
move-help2 (bp bp∷ MRootCorner d bp∷ MCornerEdge CEDDown) =
  RRight , bp bp∷ MRootCorner (RRight •r d) bp∷ MCornerEdge CEDUp
move-help2 (bp bp∷ MCornerCorner CCDUp bp∷ MCornerEdge CEDDown) =
  RRight , bp bp∷ MCornerEdge CEDRight bp∷ MEdgeEdge EEDUp
move-help2 (bp bp∷ MCornerCorner CCDRight bp∷ MCornerEdge CEDDown) =
  RRight , bp bp∷ MCornerEdge CEDDown bp∷ MEdgeEdge EEDUp
move-help2 (bp bp∷ MEdgeCorner bp∷ MCornerEdge CEDDown) =
  RRight , bp bp∷ MEdgeEdge EEDRight bp∷ MEdgeEdge EEDUp
move-help2 (bp bp∷ MEdgeEdge EEDUp) =
  RRight , bp bp∷ MEdgeCorner bp∷ MCornerEdge CEDUp
move-help2 (bp bp∷ MEdgeEdge EEDRight) =
  let d , bp' = move-help2 bp in {!   !} , bp' bp∷ MEdgeEdge EEDUp

move1 : BackPath CPRoot CPPlace → Rotation → Rotation × BackPath CPRoot CPPlace
move1 ([bp] bp∷ MRootPlace) d =
  d , [bp] bp∷ MRootCorner d bp∷ MCornerPlace CP1

move1 (bp bp∷ MCornerPlace CP1) RUp =
  RUp , bp bp∷ MCornerEdge CEDUp bp∷ MEdgePlace EP1
move1 (bp bp∷ MCornerPlace CP1) RRight =
  RUp , bp bp∷ MCornerPlace CP2
move1 (bp bp∷ m bp∷ MCornerPlace CP1) RDown =
  let r , m' = origin-place m in r r¯¹ , bp bp∷ m'
move1 ([bp] bp∷ MRootCorner d bp∷ MCornerPlace CP1) RLeft =
  RDown , [bp] bp∷ MRootCorner (RLeft •r d) bp∷ MCornerPlace CP3
move1 (bp bp∷ MCornerCorner CCDUp bp∷ MCornerPlace CP1) RLeft =
  RDown , bp bp∷ MCornerEdge CEDRight bp∷ MEdgePlace EP1
move1 (bp bp∷ MCornerCorner CCDRight bp∷ MCornerPlace CP1) RLeft =
  RRight , bp bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP1
move1 (bp bp∷ MEdgeCorner bp∷ MCornerPlace CP1) RLeft =
  RDown , bp bp∷ MEdgeEdge EEDRight bp∷ MEdgePlace EP1

move1 (bp bp∷ MCornerPlace CP2) RUp =
  RUp , bp bp∷ MCornerCorner CCDUp bp∷ MCornerPlace CP1
move1 (bp bp∷ MCornerPlace CP2) RRight =
  RRight , bp bp∷ MCornerEdge CEDRight bp∷ MEdgePlace EP1
move1 (bp bp∷ MCornerPlace CP2) RDown =
  RUp , bp bp∷ MCornerPlace CP3
move1 (bp bp∷ MCornerPlace CP2) RLeft =
  RUp , bp bp∷ MCornerPlace CP1

move1 (bp bp∷ MCornerPlace CP3) RUp =
  RUp , bp bp∷ MCornerPlace CP2
move1 (bp bp∷ MCornerPlace CP3) RRight =
  RRight , bp bp∷ MCornerCorner CCDRight bp∷ MCornerPlace CP1
move1 (bp bp∷ MCornerPlace CP3) RDown =
  RDown , bp bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP1
move1 ([bp] bp∷ MRootCorner d bp∷ MCornerPlace CP3) RLeft =
  RDown , [bp] bp∷ MRootCorner (RRight •r d) bp∷ MCornerPlace CP1
move1 (bp bp∷ MCornerCorner CCDUp bp∷ MCornerPlace CP3) RLeft =
  RDown , bp bp∷ MCornerEdge CEDRight bp∷ MEdgePlace EP1
move1 (bp bp∷ MCornerCorner CCDRight bp∷ MCornerPlace CP3) RLeft =
  RDown , bp bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP1
move1 (bp bp∷ MEdgeCorner bp∷ MCornerPlace CP3) RLeft =
  RDown , bp bp∷ MEdgeEdge EEDRight bp∷ MEdgePlace EP1

move1 (bp bp∷ MEdgePlace EP1) RUp =
  RUp , bp bp∷ MEdgeEdge EEDUp bp∷ MEdgePlace EP1
move1 (bp bp∷ MEdgePlace EP1) RRight =
  RUp , bp bp∷ MEdgePlace EP2
move1 (bp bp∷ m bp∷ MEdgePlace EP1) RDown =
  let r , m' = origin-place m in r r¯¹ , bp bp∷ m'
move1 ([bp] bp∷ MRootCorner d bp∷ MCornerEdge CEDUp bp∷ MEdgePlace EP1) RLeft =
  RLeft , [bp] bp∷ MRootCorner (RLeft •r d) bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP2
move1 (bp bp∷ MCornerCorner CCDUp bp∷ MCornerEdge CEDUp bp∷ MEdgePlace EP1) RLeft =
  RLeft , bp bp∷ MCornerEdge CEDUp bp∷ MEdgeEdge EEDRight bp∷ MEdgePlace EP2
move1 (bp bp∷ MCornerCorner CCDRight bp∷ MCornerEdge CEDUp bp∷ MEdgePlace EP1) RLeft =
  RLeft , bp bp∷ MCornerEdge CEDRight bp∷ MEdgeEdge EEDRight bp∷ MEdgePlace EP2
move1 (bp bp∷ MEdgeCorner bp∷ MCornerEdge CEDUp bp∷ MEdgePlace EP1) RLeft =
  RLeft , bp bp∷ MEdgeEdge EEDUp bp∷ MEdgeEdge EEDRight bp∷ MEdgePlace EP2
move1 (bp bp∷ MCornerEdge CEDRight bp∷ MEdgePlace EP1) RLeft =
  RDown , bp bp∷ MCornerCorner CCDUp bp∷ MCornerPlace CP3
move1 (bp bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP1) RLeft =
  RDown , bp bp∷ MCornerCorner CCDRight bp∷ MCornerPlace CP3
move1 (bp bp∷ MEdgeEdge EEDUp bp∷ MEdgePlace EP1) RLeft =
  let d , bp' = move-help1 bp in
  {!   !} , bp' bp∷ MEdgePlace EP2
move1 (bp bp∷ MEdgeEdge EEDRight bp∷ MEdgePlace EP1) RLeft =
  RDown , bp bp∷ MEdgeCorner bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP2

move1 (bp bp∷ MEdgePlace EP2) RUp =
  RUp , bp bp∷ MEdgeCorner bp∷ MCornerPlace CP1
move1 (bp bp∷ MEdgePlace EP2) RRight =
  RRight , bp bp∷ MEdgeEdge EEDRight bp∷ MEdgePlace EP1
move1 (bp bp∷ MCornerEdge CEDUp bp∷ MEdgePlace EP2) RDown =
  RRight , bp bp∷ MCornerCorner CCDUp bp∷ MCornerPlace CP1
move1 (bp bp∷ MCornerEdge CEDRight bp∷ MEdgePlace EP2) RDown =
  RRight , bp bp∷ MCornerCorner CCDRight bp∷ MCornerPlace CP1
move1 (bp bp∷ MRootCorner d bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP2) RDown =
  RRight , bp bp∷ MRootCorner (RRight •r d) bp∷ MCornerEdge CEDUp bp∷ MEdgePlace EP1
move1 (bp bp∷ MCornerCorner CCDUp bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP2) RDown =
  RRight , bp bp∷ MCornerEdge CEDRight bp∷ MEdgeEdge EEDUp bp∷ MEdgePlace EP1
move1 (bp bp∷ MCornerCorner CCDRight bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP2) RDown =
  RRight , bp bp∷ MCornerEdge CEDDown bp∷ MEdgeEdge EEDUp bp∷ MEdgePlace EP1
move1 (bp bp∷ MEdgeCorner bp∷ MCornerEdge CEDDown bp∷ MEdgePlace EP2) RDown =
  RRight , bp bp∷ MEdgeEdge EEDRight bp∷ MEdgeEdge EEDUp bp∷ MEdgePlace EP1
move1 (bp bp∷ MEdgeEdge EEDUp bp∷ MEdgePlace EP2) RDown =
  RRight , bp bp∷ MEdgeCorner bp∷ MCornerPlace CP1
move1 (bp bp∷ MEdgeEdge EEDRight bp∷ MEdgePlace EP2) RDown =
  let d , bp' = move-help1 bp in
  {!   !} , bp' bp∷ MEdgePlace EP1
move1 (bp bp∷ MEdgePlace EP2) RLeft =
  RUp , bp bp∷ MEdgePlace EP1

move+ : BackPath CPRoot CPPlace → Rotation → List Rotation → Rotation × BackPath CPRoot CPPlace
move+ bp d [l] = d , bp
move+ bp d (s ∷l ss) = let d' , bp' = move1 bp (d r¯¹ •r s) in move+ bp' (d •r d') ss

w3 : {cp₁ cp₂ : ConnectionPoint} → Move cp₁ cp₂ → Rotation × List Rotation
w3 MRootPlace = RUp , [l]
w3 (MRootCorner d) = d , d ∷l [l]
w3 (MCornerPlace CP1) = RUp , [l]
w3 (MCornerPlace CP2) = RUp , RRight ∷l [l]
w3 (MCornerPlace CP3) = RUp , RRight ∷l RDown ∷l [l]
w3 (MCornerCorner CCDUp) = RUp , RRight ∷l RUp ∷l [l]
w3 (MCornerCorner CCDRight) = RRight , RRight ∷l RDown ∷l RRight ∷l [l]
w3 (MCornerEdge CEDUp) = RUp , RUp ∷l [l]
w3 (MCornerEdge CEDRight) = RRight , RRight ∷l RRight ∷l [l]
w3 (MCornerEdge CEDDown) = RDown , RRight ∷l RDown ∷l RDown ∷l [l]
w3 (MEdgePlace EP1) = RUp , [l]
w3 (MEdgePlace EP2) = RUp , RRight ∷l [l]
w3 MEdgeCorner = RUp , RRight ∷l RUp ∷l [l]
w3 (MEdgeEdge EEDUp) = RUp , RUp ∷l [l]
w3 (MEdgeEdge EEDRight) = RRight , RRight ∷l RRight ∷l [l]

w4 : {cp : ConnectionPoint} → BackPath CPRoot CPPlace → Rotation → Path cp CPPlace → Rotation × Path CPRoot CPPlace
w4 bp d [p] = d , fwd-path bp
w4 bp d (_∷p_ m p) =
  let d' , ss = w3 m in
  let d'' , bp' = move+ bp d ss in
  w4 bp' {!   !} p

-- _•p_ : Place → Place → Place
-- (ar , ap) •p (br , bp) = move1 (backpath ap) (ar •r br •r path-rotation ap) bp

data Inspect {τ : Set} : τ → Set where

i1 : Inspect (move+ ([bp] bp∷ MRootPlace) RUp (RUp ∷l RRight ∷l RDown ∷l RLeft ∷l RUp ∷l RUp ∷l [l]))
i1 = ?

i2 : Inspect (move+ ([bp] bp∷ MRootPlace) RUp (RLeft ∷l [l]))
i2 = ?
