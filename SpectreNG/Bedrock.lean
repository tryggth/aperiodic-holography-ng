import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Function.Basic

/-- Z3 represents the quadratic integer ring ℤ[√3] as elements u + v√3. -/
@[ext]
structure Z3 where
  u : Int
  v : Int
  deriving DecidableEq, Repr

namespace Z3

def zero : Z3 := ⟨0, 0⟩
def one : Z3 := ⟨1, 0⟩
def add (x y : Z3) : Z3 := ⟨x.u + y.u, x.v + y.v⟩
def neg (x : Z3) : Z3 := ⟨-x.u, -x.v⟩
def sub (x y : Z3) : Z3 := ⟨x.u - y.u, x.v - y.v⟩
def mul (x y : Z3) : Z3 := ⟨x.u * y.u + 3 * x.v * y.v, x.u * y.v + x.v * y.u⟩
def nsmul (n : Nat) (x : Z3) : Z3 := ⟨n * x.u, n * x.v⟩
def zsmul (n : Int) (x : Z3) : Z3 := ⟨n * x.u, n * x.v⟩

instance : Zero Z3 := ⟨zero⟩
instance : One Z3 := ⟨one⟩
instance : Add Z3 := ⟨add⟩
instance : Neg Z3 := ⟨neg⟩
instance : Sub Z3 := ⟨sub⟩
instance : Mul Z3 := ⟨mul⟩

@[simp] lemma add_def (x y : Z3) : x + y = add x y := rfl
@[simp] lemma neg_def (x : Z3) : -x = neg x := rfl
@[simp] lemma sub_def (x y : Z3) : x - y = sub x y := rfl
@[simp] lemma mul_def (x y : Z3) : x * y = mul x y := rfl
@[simp] lemma zero_def : (0 : Z3) = zero := rfl
@[simp] lemma one_def : (1 : Z3) = one := rfl

instance : CommRing Z3 where
  add_assoc _ _ _ := by ext <;> simp [add] <;> ring
  zero_add _ := by ext <;> simp [add, zero]
  add_zero _ := by ext <;> simp [add, zero]
  neg_add_cancel _ := by ext <;> simp [add, neg, zero]
  add_comm _ _ := by ext <;> simp [add] <;> ring
  mul_assoc _ _ _ := by ext <;> simp [mul] <;> ring
  one_mul _ := by ext <;> simp [mul, one]
  mul_one _ := by ext <;> simp [mul, one]
  left_distrib _ _ _ := by ext <;> simp [add, mul] <;> ring
  right_distrib _ _ _ := by ext <;> simp [add, mul] <;> ring
  mul_comm _ _ := by ext <;> simp [mul] <;> ring
  zero_mul _ := by ext <;> simp [mul, zero]
  mul_zero _ := by ext <;> simp [mul, zero]
  sub_eq_add_neg _ _ := rfl
  nsmul := nsmul
  nsmul_zero _ := by ext <;> simp [nsmul, zero]
  nsmul_succ n x := by ext <;> simp [nsmul, add] <;> ring
  zsmul := zsmul
  zsmul_zero' _ := by ext <;> simp [zsmul, zero]
  zsmul_succ' n x := by ext <;> simp [zsmul, add] <;> ring
  zsmul_neg' n x := by ext <;> simp [zsmul, neg] <;> rw [Int.negSucc_eq] <;> ring

end Z3

/-- LatticePoint represents a point in the 4D cyclotomic lattice ℤ[ζ_12]. -/
@[ext]
structure LatticePoint where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace LatticePoint

def zero : LatticePoint := ⟨0, 0, 0, 0⟩
def add (x y : LatticePoint) : LatticePoint := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def neg (x : LatticePoint) : LatticePoint := ⟨-x.a, -x.b, -x.c, -x.d⟩
def sub (x y : LatticePoint) : LatticePoint := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩

instance : Zero LatticePoint := ⟨zero⟩
instance : Add LatticePoint := ⟨add⟩
instance : Neg LatticePoint := ⟨neg⟩
instance : Sub LatticePoint := ⟨sub⟩

/-- Rotates the lattice point by 30 degrees. -/
def rot30 (pt : LatticePoint) : LatticePoint :=
  ⟨-pt.d, pt.a, pt.b + pt.d, pt.c⟩

/-- Prove that applying rot30 12 times returns the point to itself. -/
theorem rot30_twelve_cycles (p : LatticePoint) : (rot30^[12]) p = p := by
  ext <;> dsimp [rot30] <;> ring

end LatticePoint
