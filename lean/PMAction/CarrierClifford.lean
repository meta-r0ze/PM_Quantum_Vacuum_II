import PMAction.CarrierVacuumSector

/-! The native generators obey Clifford relations on the complete intrinsic
coordinate-odd sector. They are not asserted to be a Clifford representation
on all eight carrier labels; that would contradict the uniform-mode obstruction. -/
noncomputable section
namespace PMAction.CarrierClifford
open Matrix CarrierVacuumSector

private lemma product_action {a b : Type*} [Fintype a] [Fintype b]
    (A B : Matrix a a ℂ) (E : Matrix a b ℂ) (A' B' : Matrix b b ℂ)
    (ha : A*E=E*A') (hb : B*E=E*B') : (A*B)*E=E*(A'*B') := by
  rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]

theorem alpha_square (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2) (j : Fin 3) :
    (alpha c p j * alpha c p j) * CarrierParity.embedding c = CarrierParity.embedding c := by
  rw [product_action _ _ _ _ _ (alpha_intertwining c p hp hp1 j)
    (alpha_intertwining c p hp hp1 j), ConcreteFermion.clifford.1 j, Matrix.mul_one]

theorem beta_square (c : Fin 3) :
    (beta c * beta c) * CarrierParity.embedding c = CarrierParity.embedding c := by
  rw [product_action _ _ _ _ _ (beta_intertwining c) (beta_intertwining c),
    ConcreteFermion.beta_square, Matrix.mul_one]

theorem gamma_square (c : Fin 3) :
    (gamma c * gamma c) * CarrierParity.embedding c = CarrierParity.embedding c := by
  rw [product_action _ _ _ _ _ (gamma_intertwining c) (gamma_intertwining c),
    ConcreteFermion.gamma_square, Matrix.mul_one]

theorem alpha_anticommutes (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2)
    (j k : Fin 3) (hjk : j≠k) :
    (alpha c p j * alpha c p k + alpha c p k * alpha c p j) * CarrierParity.embedding c = 0 := by
  rw [Matrix.add_mul,
    product_action _ _ _ _ _ (alpha_intertwining c p hp hp1 j) (alpha_intertwining c p hp hp1 k),
    product_action _ _ _ _ _ (alpha_intertwining c p hp hp1 k) (alpha_intertwining c p hp hp1 j),
    ← Matrix.mul_add, ConcreteFermion.clifford.2.2.1 j k hjk, Matrix.mul_zero]

theorem alpha_beta (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2) (j : Fin 3) :
    (alpha c p j * beta c + beta c * alpha c p j) * CarrierParity.embedding c = 0 := by
  rw [Matrix.add_mul,
    product_action _ _ _ _ _ (alpha_intertwining c p hp hp1 j) (beta_intertwining c),
    product_action _ _ _ _ _ (beta_intertwining c) (alpha_intertwining c p hp hp1 j),
    ← Matrix.mul_add, ConcreteFermion.clifford.2.2.2 j, Matrix.mul_zero]

theorem alpha_gamma (c : Fin 3) (p : ℝ) (hp : 0<p) (hp1 : p<1/2) (j : Fin 3) :
    (alpha c p j * gamma c) * CarrierParity.embedding c =
      (gamma c * alpha c p j) * CarrierParity.embedding c := by
  rw [product_action _ _ _ _ _ (alpha_intertwining c p hp hp1 j) (gamma_intertwining c),
    product_action _ _ _ _ _ (gamma_intertwining c) (alpha_intertwining c p hp hp1 j),
    ConcreteFermion.alpha_gamma]

theorem beta_gamma (c : Fin 3) :
    (beta c * gamma c + gamma c * beta c) * CarrierParity.embedding c = 0 := by
  rw [Matrix.add_mul,
    product_action _ _ _ _ _ (beta_intertwining c) (gamma_intertwining c),
    product_action _ _ _ _ _ (gamma_intertwining c) (beta_intertwining c),
    ← Matrix.mul_add, ConcreteFermion.beta_gamma, neg_add_cancel, Matrix.mul_zero]

end PMAction.CarrierClifford
