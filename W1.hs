{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures #-}

module W1 where

import Data.Kind

data Rotation = RUp | RRight | RDown | RLeft
data CornerCornerDir = CCDUp | CCDRight
data CornerEdgeDir = CEDUp | CEDRight | CEDDown
data CornerPlace = CP1 | CP2 | CP3
data EdgeEdgeDir = EEDUp | EEDRight
data EdgePlace = EP1 | EP2
data ConnectionPoint = CPRoot | CPPlace | CPCorner | CPEdge
data Move :: ConnectionPoint -> ConnectionPoint -> Type where
	MRootPlace :: Move CPRoot CPPlace
	MRootCorner :: Rotation -> Move CPRoot CPCorner
	MCornerPlace :: CornerPlace -> Move CPCorner CPPlace
	MCornerCorner :: CornerCornerDir -> Move CPCorner CPCorner
	MCornerEdge :: CornerEdgeDir -> Move CPCorner CPEdge
	MEdgePlace :: EdgePlace -> Move CPEdge CPPlace
	MEdgeCorner :: Move CPEdge CPCorner
	MEdgeEdge :: EdgeEdgeDir -> Move CPEdge CPEdge
infixr 5 :<
data Path :: ConnectionPoint -> ConnectionPoint -> Type where
	PNil :: Path cp cp
	(:<) :: Move cp1 cp2 -> Path cp2 cp3 -> Path cp1 cp3
infixl 5 :>
data BackPath :: ConnectionPoint -> ConnectionPoint -> Type where
	BPNil :: BackPath cp cp
	(:>) :: BackPath cp1 cp2 -> Move cp2 cp₃ -> BackPath cp1 cp₃
type Place = (Rotation, Path CPRoot CPPlace)

moveRotation :: Move cp1 cp2 -> Rotation
moveRotation MRootPlace = RUp
moveRotation (MRootCorner d) = d
moveRotation (MCornerPlace p) = RUp
moveRotation (MCornerCorner CCDUp) = RUp
moveRotation (MCornerCorner CCDRight) = RRight
moveRotation (MCornerEdge CEDUp) = RUp
moveRotation (MCornerEdge CEDRight) = RRight
moveRotation (MCornerEdge CEDDown) = RDown
moveRotation (MEdgePlace p) = RUp
moveRotation MEdgeCorner = RUp
moveRotation (MEdgeEdge EEDUp) = RUp
moveRotation (MEdgeEdge EEDRight) = RRight

instance Semigroup Rotation where
	RUp <> b = b
	RRight <> RUp = RRight
	RRight <> RRight = RDown
	RRight <> RDown = RLeft
	RRight <> RLeft = RUp
	RDown <> RUp = RDown
	RDown <> RRight = RLeft
	RDown <> RDown = RUp
	RDown <> RLeft = RRight
	RLeft <> RUp = RLeft
	RLeft <> RRight = RUp
	RLeft <> RDown = RRight
	RLeft <> RLeft = RDown
instance Monoid Rotation where
	mempty = RUp
rotInv :: Rotation -> Rotation
rotInv RUp = RUp
rotInv RRight = RLeft
rotInv RDown = RDown
rotInv RLeft = RRight
pathRotation :: Path cp1 cp2 -> Rotation
pathRotation PNil = RUp
pathRotation (m :< p) = moveRotation m <> pathRotation p
pathSnoc :: Path cp1 cp2 -> Move cp2 cp3 -> Path cp1 cp3
pathSnoc PNil m = m :< PNil
pathSnoc (m' :< p) m = m' :< pathSnoc p m
backpathCons :: Move cp1 cp2 -> BackPath cp2 cp3 -> BackPath cp1 cp3
backpathCons m BPNil = BPNil :> m
backpathCons m (bp :> m') = backpathCons m bp :> m'
backpath :: Path cp1 cp2 -> BackPath cp1 cp2
backpath PNil = BPNil
backpath (m :< p) = backpathCons m (backpath p)
fwdPath :: BackPath cp1 cp2 -> Path cp1 cp2
fwdPath BPNil = PNil
fwdPath (bp :> m) = pathSnoc (fwdPath bp) m
originPlace :: Move cp1 cp2 -> (Rotation, Move cp1 CPPlace)
originPlace MRootPlace = (RUp, MRootPlace)
originPlace (MRootCorner d) = (d, MRootPlace)
originPlace (MCornerPlace i) = (RUp, MCornerPlace i)
originPlace (MCornerCorner CCDUp) = (RUp, MCornerPlace CP2)
originPlace (MCornerCorner CCDRight) = (RRight, MCornerPlace CP3)
originPlace (MCornerEdge CEDUp) = (RUp, MCornerPlace CP1)
originPlace (MCornerEdge CEDRight) = (RRight, MCornerPlace CP2)
originPlace (MCornerEdge CEDDown) = (RDown, MCornerPlace CP3)
originPlace (MEdgePlace i) = (RUp, MEdgePlace i)
originPlace MEdgeCorner = (RUp, MEdgePlace EP2)
originPlace (MEdgeEdge EEDUp) = (RUp, MEdgePlace EP1)
originPlace (MEdgeEdge EEDRight) = (RRight, MEdgePlace EP2)

move1 :: BackPath CPRoot CPPlace -> Rotation -> (Rotation, BackPath CPRoot CPPlace)
move1 (BPNil :> MRootPlace) d =
	(d, BPNil :> MRootCorner d :> MCornerPlace CP1)

move1 (bp :> MCornerPlace CP1) RUp =
	(RUp, bp :> MCornerEdge CEDUp :> MEdgePlace EP1)
move1 (bp :> MCornerPlace CP1) RRight =
	(RUp, bp :> MCornerPlace CP2)
move1 (bp :> m :> MCornerPlace CP1) RDown =
	let (r, m') = origin-place m in (rotInv r, bp :> m')
move1 (BPNil :> MRootCorner d :> MCornerPlace CP1) RLeft =
	(RDown, BPNil :> MRootCorner (RLeft <> d) :> MCornerPlace CP3)
move1 (bp :> MCornerCorner CCDUp :> MCornerPlace CP1) RLeft =
	(RDown, bp :> MCornerEdge CEDRight :> MEdgePlace EP1)
move1 (bp :> MCornerCorner CCDRight :> MCornerPlace CP1) RLeft =
	(RRight, bp :> MCornerEdge CEDDown :> MEdgePlace EP1)
move1 (bp :> MEdgeCorner :> MCornerPlace CP1) RLeft =
	(RDown, bp :> MEdgeEdge EEDRight :> MEdgePlace EP1)

move1 (bp :> MCornerPlace CP2) RUp =
	(RUp, bp :> MCornerCorner CCDUp :> MCornerPlace CP1)
move1 (bp :> MCornerPlace CP2) RRight =
	(RRight, bp :> MCornerEdge CEDRight :> MEdgePlace EP1)
move1 (bp :> MCornerPlace CP2) RDown =
	(RUp, bp :> MCornerPlace CP3)
move1 (bp :> MCornerPlace CP2) RLeft =
	(RUp, bp :> MCornerPlace CP1)

move1 (bp :> MCornerPlace CP3) RUp =
	(RUp, bp :> MCornerPlace CP2)
move1 (bp :> MCornerPlace CP3) RRight =
	(RRight, bp :> MCornerCorner CCDRight :> MCornerPlace CP1)
move1 (bp :> MCornerPlace CP3) RDown =
	(RDown, bp :> MCornerEdge CEDDown :> MEdgePlace EP1)
move1 (BPNil :> MRootCorner d :> MCornerPlace CP3) RLeft =
	(RDown, BPNil :> MRootCorner (RRight <> d) :> MCornerPlace CP1)
move1 (bp :> MCornerCorner CCDUp :> MCornerPlace CP3) RLeft =
	(RDown, bp :> MCornerEdge CEDRight :> MEdgePlace EP1)
move1 (bp :> MCornerCorner CCDRight :> MCornerPlace CP3) RLeft =
	(RDown, bp :> MCornerEdge CEDDown :> MEdgePlace EP1)
move1 (bp :> MEdgeCorner :> MCornerPlace CP3) RLeft =
	(RDown, bp :> MEdgeEdge EEDRight :> MEdgePlace EP1)

move1 (bp :> MEdgePlace EP1) RUp =
	(RUp, bp :> MEdgeEdge EEDUp :> MEdgePlace EP1)
move1 (bp :> MEdgePlace EP1) RRight =
	(RUp, bp :> MEdgePlace EP2)
move1 (bp :> m :> MEdgePlace EP1) RDown =
	let (r, m') = origin-place m in (rotInv r, bp :> m')
move1 (BPNil :> MRootCorner d :> MCornerEdge CEDUp :> MEdgePlace EP1) RLeft =
	(RLeft, BPNil :> MRootCorner (RLeft <> d) :> MCornerEdge CEDDown :> MEdgePlace EP2)
move1 (bp :> MCornerCorner CCDUp :> MCornerEdge CEDUp :> MEdgePlace EP1) RLeft =
	(RLeft, bp :> MCornerEdge CEDUp :> MEdgeEdge EEDRight :> MEdgePlace EP2)
move1 (bp :> MCornerCorner CCDRight :> MCornerEdge CEDUp :> MEdgePlace EP1) RLeft =
	(RLeft, bp :> MCornerEdge CEDRight :> MEdgeEdge EEDRight :> MEdgePlace EP2)
move1 (bp :> MEdgeCorner :> MCornerEdge CEDUp :> MEdgePlace EP1) RLeft =
	(RLeft, bp :> MEdgeEdge EEDUp :> MEdgeEdge EEDRight :> MEdgePlace EP2)
move1 (bp :> MCornerEdge CEDRight :> MEdgePlace EP1) RLeft =
	(RDown, bp :> MCornerCorner CCDUp :> MCornerPlace CP3)
move1 (bp :> MCornerEdge CEDDown :> MEdgePlace EP1) RLeft =
	(RDown, bp :> MCornerCorner CCDRight :> MCornerPlace CP3)
move1 (bp :> MEdgeEdge EEDUp :> MEdgePlace EP1) RLeft =
	let (d, bp') = go bp in
	(_, bp' :> MEdgePlace EP2)
	where
		-- rightmost edge of next left node
		go :: BackPath CPRoot CPEdge -> (Rotation, BackPath CPRoot CPEdge)
		go (BPNil :> MRootCorner d :> MCornerEdge CEDUp) =
			(RLeft, BPNil :> MRootCorner (RLeft •r d) :> MCornerEdge CEDDown :> MEdgeEdge EEDRight)
		go (bp :> MCornerCorner CCDUp :> MCornerEdge CEDUp) =
			(RLeft, bp :> MCornerEdge CEDUp :> MEdgeEdge EEDRight :> MEdgeEdge EEDRight)
		go (bp :> MCornerCorner CCDRight :> MCornerEdge CEDUp) =
			(RLeft, bp :> MCornerEdge CEDRight :> MEdgeEdge EEDRight :> MEdgeEdge EEDRight)
		go (bp :> MEdgeCorner :> MCornerEdge CEDUp) =
			(RLeft, bp :> MEdgeEdge EEDUp :> MEdgeEdge EEDRight :> MEdgeEdge EEDRight)
		go (bp :> MCornerEdge CEDRight) =
			(RDown, bp :> MCornerCorner CCDUp :> MCornerEdge CEDDown)
		go (bp :> MCornerEdge CEDDown) =
			(RDown, bp :> MCornerCorner CCDRight :> MCornerEdge CEDDown)
		go (bp :> MEdgeEdge EEDUp) =
			let (d, bp') = go bp in
			(_, bp' :> MEdgeEdge EEDUp)
		go (bp :> MEdgeEdge EEDRight) =
			(RDown, bp :> MEdgeCorner :> MCornerEdge CEDDown :> MEdgeEdge EEDRight)
move1 (bp :> MEdgeEdge EEDRight :> MEdgePlace EP1) RLeft =
	(RDown, bp :> MEdgeCorner :> MCornerEdge CEDDown :> MEdgePlace EP2)

move1 (bp :> MEdgePlace EP2) RUp =
	(RUp, bp :> MEdgeCorner :> MCornerPlace CP1)
move1 (bp :> MEdgePlace EP2) RRight =
	(RRight, bp :> MEdgeEdge EEDRight :> MEdgePlace EP1)
move1 (bp :> MCornerEdge CEDUp :> MEdgePlace EP2) RDown =
	(RRight, bp :> MCornerCorner CCDUp :> MCornerPlace CP1)
move1 (bp :> MCornerEdge CEDRight :> MEdgePlace EP2) RDown =
	(RRight, bp :> MCornerCorner CCDRight :> MCornerPlace CP1)
move1 (bp :> MRootCorner d :> MCornerEdge CEDDown :> MEdgePlace EP2) RDown =
	(RRight, bp :> MRootCorner (RRight <> d) :> MCornerEdge CEDUp :> MEdgePlace EP1)
move1 (bp :> MCornerCorner d :> MCornerEdge CEDDown :> MEdgePlace EP2) RDown = _
move1 (bp :> MEdgeCorner :> MCornerEdge CEDDown :> MEdgePlace EP2) RDown = _
move1 (bp :> MEdgeEdge d :> MEdgePlace EP2) RDown = _
move1 (bp :> MEdgePlace EP2) RLeft =
	(RUp, bp :> MEdgePlace EP1)
