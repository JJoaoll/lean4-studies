
inductive Side where
| white
| black
deriving Repr

inductive Pos where
| x
deriving Repr

-- inductive Piece (s : Side) where
-- | pawn
-- | knight
-- | bishop
-- | rook
-- | queen
-- | king
-- deriving Repr

inductive Piece where
| pawn   : Pos → Side → Piece
| knight : Pos → Side → Piece
| bishop : Pos → Side → Piece
| rook   : Pos → Side → Piece
| queen  : Pos → Side → Piece
| king   : Pos → Side → Piece
deriving Repr
open Piece

#check pawn
#check pawn Pos.x Side.white
