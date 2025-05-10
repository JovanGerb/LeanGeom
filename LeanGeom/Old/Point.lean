import LeanGeom.Defs
import LeanGeom.Equivalence

namespace LeanGeom

instance : EqType Point where
  EqProof := PointEq
  refl := .refl
  symm := .symm
  trans := .trans

instance : Atomic Point where
instance : Object Point := baseObject

variable {m} [Monad m] [MonadReaderOf (IO.Ref (UnionFind Point)) m] [MonadLift IO m]

instance : BaseObject m Point where
  Abstraction := by exact UFObject Point
