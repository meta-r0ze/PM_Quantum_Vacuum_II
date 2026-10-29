import PMAction.GaugeRecordEmbedding

/-!
# Local gauge frames for transported reference packets

Independent frames at neighbouring sites require transforming link matrices.
The matrix-valued link law is proved covariant, norm preserving for unitary
links, and reversible. A transported reference remains covariant rather than
being required to be a nonzero gauge-invariant vector. No particular physical
connection or vacuum source is selected by these identities.
-/
noncomputable section
namespace PMAction.GaugeRecordLinks
open Matrix
variable {X n : Type*} [Fintype n] [DecidableEq n]

abbrev Packet (n : Type*) := n → ℂ

def frame (g : X → Matrix n n ℂ) (ψ : X → Packet n) : X → Packet n := fun x => g x *ᵥ ψ x

def transport (e : Equiv.Perm X) (L : X → Matrix n n ℂ) (ψ : X → Packet n) : X → Packet n :=
  fun x => L x *ᵥ ψ (e x)

/-- Output and source frames may differ, also allowing a temporal link. -/
def transformed (e : Equiv.Perm X) (outFrame inFrame L : X → Matrix n n ℂ) : X → Matrix n n ℂ :=
  fun x => outFrame x * L x * (inFrame (e x))ᴴ

/-- The non-Abelian link law follows from the actual transported packet action. -/
theorem covariance (e : Equiv.Perm X) (outFrame inFrame L : X → Matrix n n ℂ)
    (hin : ∀ x, inFrame x ∈ unitary (Matrix n n ℂ)) (ψ : X → Packet n) :
    transport e (transformed e outFrame inFrame L) (frame inFrame ψ) =
      frame outFrame (transport e L ψ) := by
  funext x
  change (outFrame x * L x * (inFrame (e x))ᴴ) *ᵥ (inFrame (e x) *ᵥ ψ (e x)) = _
  have hi : (inFrame (e x))ᴴ * inFrame (e x) = 1 := (hin (e x)).1
  rw [mulVec_mulVec, Matrix.mul_assoc, hi, mul_one, ← mulVec_mulVec]
  rfl

/-- Changing unitary frames preserves admissibility of a unitary link. -/
theorem transformed_unitary (e : Equiv.Perm X) (outFrame inFrame L : X → Matrix n n ℂ)
    (hout : ∀ x, outFrame x ∈ unitary (Matrix n n ℂ))
    (hin : ∀ x, inFrame x ∈ unitary (Matrix n n ℂ))
    (hL : ∀ x, L x ∈ unitary (Matrix n n ℂ)) (x : X) :
    transformed e outFrame inFrame L x ∈ unitary (Matrix n n ℂ) := by
  have hs : (inFrame (e x))ᴴ ∈ unitary (Matrix n n ℂ) := by
    have hl : (inFrame (e x))ᴴ * inFrame (e x) = 1 := (hin _).1
    have hr : inFrame (e x) * (inFrame (e x))ᴴ = 1 := (hin _).2
    constructor
    · simpa [star_eq_conjTranspose] using hr
    · simpa [star_eq_conjTranspose] using hl
  exact (unitary _).mul_mem ((unitary _).mul_mem (hout x) (hL x)) hs

/-- Inverting the links reconstructs every packet, not only the reference. -/
theorem reverse_transport (e : Equiv.Perm X) (L : X → Matrix n n ℂ)
    (hL : ∀ x, L x ∈ unitary (Matrix n n ℂ)) (ψ : X → Packet n) :
    transport e⁻¹ (fun x => (L (e⁻¹ x))ᴴ) (transport e L ψ) = ψ := by
  funext x
  simp only [transport]
  rw [mulVec_mulVec, show (L (e⁻¹ x))ᴴ * L (e⁻¹ x) = 1 from (hL _).1, one_mulVec]
  simp

/-- Finite-array norm is conserved by arbitrary supplied unitary payload links. -/
theorem population_preserved [Fintype X] (e : Equiv.Perm X) (L : X → Matrix n n ℂ)
    (hL : ∀ x, L x ∈ unitary (Matrix n n ℂ)) (ψ : X → Packet n) :
    (∑ x, CommonResponse.nsq (transport e L ψ x)) = ∑ x, CommonResponse.nsq (ψ x) := by
  have h (x : X) : CommonResponse.nsq (transport e L ψ x) = CommonResponse.nsq (ψ (e x)) :=
    congrArg Complex.re (CommonResponse.unitary_nsq _ (hL x) _)
  simp_rw [h]
  exact Equiv.sum_comp e (fun x : X => CommonResponse.nsq (ψ x))

/-- Changing frames preserves reference maintenance if the reference is transformed too. -/
theorem reference_covariance (e : Equiv.Perm X) (g L : X → Matrix n n ℂ)
    (hg : ∀ x, g x ∈ unitary (Matrix n n ℂ)) (reference : X → Packet n)
    (href : transport e L reference = reference) :
    transport e (transformed e g g L) (frame g reference) = frame g reference := by
  rw [covariance e g g L hg, href]

/-- A witness with nonuniform local frames; this does not assert that every physical link is flat. -/
theorem framed_reference_train (e : Equiv.Perm X) (g : X → Matrix n n ℂ)
    (hg : ∀ x, g x ∈ unitary (Matrix n n ℂ)) (r : Packet n) :
    transport e (transformed e g g (fun _ => 1)) (frame g (fun _ => r)) =
      frame g (fun _ => r) := by
  apply reference_covariance e g (fun _ => 1) hg
  funext x
  simp [transport]

end PMAction.GaugeRecordLinks
