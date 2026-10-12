import QZeta3.Imports

/-!
# The concrete q-Catalan data

Definitions follow the 12 October 2026 manuscript at source commit `c44abf1`.
The target is the Lambert-series normalization of Jouhet and Mosaki, not the
combinatorial q-Catalan numbers or the classical Catalan constant.
-/

open Polynomial Finset

namespace QCatalan

/-- The nontrivial character modulo four. -/
def chi (n : ℕ) : ℤ := if n % 2 = 0 then 0 else (-1) ^ (n / 2)

/-- The unshifted summand of the paper's positive convergent series. -/
noncomputable def term (p n : ℕ) : ℝ :=
  (n : ℝ) * (p : ℝ) ^ n / ((p : ℝ) ^ (2 * n) + 1)

/-- The target; convergence must be proved separately to exclude `tsum`'s default value. -/
noncomputable def xi (p : ℕ) : ℝ := ∑' n : ℕ, term p (n + 1)

/-- The polynomial moments of the signed first Euler derivative functional. -/
def mu (p j : ℕ) : ℚ := (j : ℚ) * (p : ℚ) ^ j / (1 + (p : ℚ) ^ (2 * j))

/-- `g₂(y) = y/(1-y)²`. -/
def g2 (y : ℚ) : ℚ := y / (1 - y) ^ 2

/-- The finite character tail; reciprocal symmetry allows positive powers of `p`. -/
def S (p N : ℕ) : ℚ := ∑ b ∈ Icc 1 N, (chi b : ℚ) * g2 ((p : ℚ) ^ b)

def Lpoly (p : ℕ) (f : ℚ[X]) : ℚ := ∑ j ∈ f.support, f.coeff j * mu p j

/-- The monic denominator has nodes `p^(2a)`. -/
noncomputable def F (p K : ℕ) : ℚ[X] :=
  ∏ a ∈ Icc 1 K, (X - C ((p : ℚ) ^ (2 * a)))

noncomputable def res (p K k a : ℕ) : ℚ :=
  (p : ℚ) ^ (2 * a * k) / (derivative (F p K)).eval ((p : ℚ) ^ (2 * a))

/-- Constant coefficient of the complete partial-fraction functional, including its quotient. -/
noncomputable def mConst (p K k : ℕ) : ℚ :=
  Lpoly p (X ^ k /ₘ F p K) +
    ∑ a ∈ Icc 1 K, res p K k a * (-1) ^ a * S p (2 * a) / (p : ℚ) ^ (2 * a)

/-- Coefficient of the target variable in the same functional. -/
noncomputable def mLin (p K k : ℕ) : ℚ :=
  -∑ a ∈ Icc 1 K, res p K k a * (-1) ^ a / (p : ℚ) ^ (2 * a)

def nrm (p K : ℕ) : ℚ := (-1) ^ K * (p : ℚ) ^ (K * (K + 1))

noncomputable def hankelLin (p K : ℕ) : Matrix (Fin K) (Fin K) ℚ :=
  Matrix.of fun i j => nrm p K * mLin p K (i.val + j.val)

noncomputable def hankelConst (p K : ℕ) : Matrix (Fin K) (Fin K) ℚ :=
  Matrix.of fun i j => nrm p K * mConst p K (i.val + j.val)

noncomputable def Delta (p K : ℕ) : ℚ[X] :=
  Matrix.det ((X : ℚ[X]) • (hankelLin p K).map C + (hankelConst p K).map C)

noncomputable def DeltaR (p K : ℕ) (x : ℝ) : ℝ := aeval x (Delta p K)

/-- Exact content exponent as a finite sum, avoiding signed-natural division. -/
def cK (K : ℕ) : ℕ :=
  K ^ 2 * (K + 1) - ∑ i ∈ range K, (K - 2 * i) * (K - 2 * i + 1)

/-- Sum of the root exponents in the double-root basis. -/
def aj (j : ℕ) : ℕ := ∑ t ∈ Icc 1 j, (2 * ((t + 1) / 2) - 1)

def bK (K : ℕ) : ℕ := 2 * ∑ j ∈ range K, aj j

def clusterCost (m : ℕ) : ℕ := if m = 0 then 0 else (m + 2) ^ 2 / 4

/-- The exact cyclotomic exponent in equation (4.1); the unused order zero is set to zero. -/
def E (K d : ℕ) : ℕ :=
  if d = 0 then 0 else
  if d % 2 = 1 then
    if d ≤ K then
      (K % d) * clusterCost (K / d + 1) + (d - K % d) * clusterCost (K / d)
    else if d ≤ 2 * K then 2 * (K - (d - 1) / 2) else 0
  else if d % 4 = 2 then
    ∑ a ∈ Icc 1 K, if a % 2 = 1 then K - a * (d / 2) else 0
  else min K ((K - 4 * (d / 4)) + (K - (d / 4) - 1))

noncomputable def Phi (p d : ℕ) : ℤ := (cyclotomic d ℤ).eval (p : ℤ)

noncomputable def CK (p K : ℕ) : ℤ := ∏ d ∈ Icc 1 (4 * K), Phi p d ^ E K d

/-- The normalized polynomial, initially defined over the rationals. -/
noncomputable def PK (p K : ℕ) : ℚ[X] :=
  Delta p K * C ((CK p K : ℚ) / (p : ℚ) ^ cK K)

noncomputable def cost : ℝ := 1 / 6 + 1309 / (150 * Real.pi ^ 2)

noncomputable def margin : ℝ := 1 - 1309 / (150 * Real.pi ^ 2)

end QCatalan
