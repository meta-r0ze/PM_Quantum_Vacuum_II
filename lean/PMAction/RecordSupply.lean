import PMAction.NativeReferenceBackground

/-!
# Where the clean records come from

`RecordTransport` (and Paper III's `RecordRenewal`) shows exact maintenance over `T` cycles needs `T`
clean records. The native protocol (`NativeCarrierProtocol`) streams live labels forward and
record labels backward. At the coupling site the live value is replaced by the arriving record,
and the departing live value becomes a record.

This module follows the two streams through the coupling site. It needs no finiteness of the
substrate.

* `live_at_site`: after `t` ticks, the live value at the coupling site is the record that started
  at `eᵗ o`, provided the backward stream has not returned to `o` in the meantime.
* `clean_supply`: so if the record cells upstream of the site carry the reference, the site's live
  value is the reference at every tick, whatever disturbances arrive on the live stream. A
  stationary background (`NativeReferenceBackground.stationary_iff`) has every record equal to the
  reference, so it is such a supply.
* `disturbance_exported`: each arriving live disturbance is not erased. It is written into the
  record leaving the site, and carried away along the backward stream.
* `open_orbit_forever`: on an orbit that never returns (for example `X = ℤ`, `e = succ`), the
  repair is exact at every tick.
* `ring_returns`: on a ring of `N` sites, a disturbance stored at tick `1` comes back to the live
  output at tick `N + 1`. This is the finite-supply bound of `RecordRenewal`.

* `translation_open`, `lattice_forever`: on the infinite lattice `ℤᵈ` with translation routing
  along any nonzero vector (a D₄ root), the backward stream is open, so maintenance is exact
  forever.

So the incoming record stream is the backward stream of the stationary background. Exact
maintenance forever needs an open orbit, and lattice translation routing gives one. Still
inputs: that the routing is a lattice translation on the unbounded lattice, and the background's
normalization.
-/

noncomputable section
namespace PMAction.RecordSupply

variable {X A : Type*} [DecidableEq X]

/-- One tick on (live, record) pairs, as `NativeReferenceBackground.advance`, without
finiteness. -/
def step (o : X) (e : Equiv.Perm X) (s : X → A × A) : X → A × A :=
  fun x => if x = o then ((s (e x)).2, (s (e⁻¹ x)).1) else ((s (e⁻¹ x)).1, (s (e x)).2)

/-- `t` ticks. -/
def run (o : X) (e : Equiv.Perm X) : ℕ → (X → A × A) → X → A × A
  | 0, s => s
  | t + 1, s => step o e (run o e t s)

/-- The backward stream from `eᵏ o` stays away from `o` for `t` steps. -/
def Clear (o : X) (e : Equiv.Perm X) (k t : ℕ) : Prop := ∀ j, j < t → (e ^ (k + j)) o ≠ o

lemma run_succ (o : X) (e : Equiv.Perm X) (t : ℕ) (s : X → A × A) :
    run o e (t + 1) s = step o e (run o e t s) := rfl

lemma run_add (o : X) (e : Equiv.Perm X) (s : X → A × A) (a b : ℕ) :
    run o e (b + a) s = run o e b (run o e a s) := by
  induction b with
  | zero => simp [run]
  | succ b ih => rw [show b + 1 + a = (b + a) + 1 by omega, run_succ, ih, run_succ]

omit [DecidableEq X] in
lemma pow_succ_apply (e : Equiv.Perm X) (k : ℕ) (x : X) : (e ^ (k + 1)) x = e ((e ^ k) x) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

/-- **Records flow backward unchanged** until they reach the coupling site. -/
lemma record_path (o : X) (e : Equiv.Perm X) (s : X → A × A) :
    ∀ t k : ℕ, Clear o e k t → (run o e t s ((e ^ k) o)).2 = (s ((e ^ (k + t)) o)).2 := by
  intro t
  induction t with
  | zero => intro k _; simp [run]
  | succ t ih =>
    intro k hk
    have hne : (e ^ k) o ≠ o := by simpa using hk 0 (by omega)
    have hk' : Clear o e (k + 1) t := fun j hj => by
      have := hk (j + 1) (by omega); rwa [show k + (j + 1) = k + 1 + j by omega] at this
    rw [run_succ]
    simp only [step, hne, ite_false]
    rw [← pow_succ_apply, ih (k + 1) hk', show k + 1 + t = k + (t + 1) by omega]

/-- **The live value at the coupling site** after `t + 1` ticks is the record that started at
`e^{t+1} o`. -/
theorem live_at_site (o : X) (e : Equiv.Perm X) (s : X → A × A) (t : ℕ) (h : Clear o e 1 t) :
    (run o e (t + 1) s o).1 = (s ((e ^ (t + 1)) o)).2 := by
  rw [run_succ]
  simp only [step, ite_true]
  have := record_path o e s t 1 h
  rw [pow_one] at this
  rw [this, add_comm]

/-- **Clean records upstream repair the site.** Whatever the live stream brings, the live value at
`o` is the reference at every tick `1 ≤ t ≤ T`, provided the `T` upstream record cells carry the
reference and the backward stream does not return within `T` steps. -/
theorem clean_supply (o : X) (e : Equiv.Perm X) (s : X → A × A) (r : A) (T : ℕ)
    (hclean : ∀ m, 1 ≤ m → m ≤ T → (s ((e ^ m) o)).2 = r)
    (hopen : ∀ m, 1 ≤ m → m < T → (e ^ m) o ≠ o) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) :
    (run o e t s o).1 = r := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [live_at_site o e s t' (fun j hj => hopen (1 + j) (by omega) (by omega))]
  exact hclean (t' + 1) (by omega) htT

/-- **Disturbances are exported, not erased.** The record leaving the site holds the live value
that arrived. -/
theorem disturbance_exported (o : X) (e : Equiv.Perm X) (s : X → A × A) (t : ℕ) :
    (run o e (t + 1) s o).2 = (run o e t s (e⁻¹ o)).1 := by
  simp [run_succ, step]

/-- **An open orbit repairs forever.** If the backward stream never returns and every record
starts at the reference, the site's live value is the reference at every tick. -/
theorem open_orbit_forever (o : X) (e : Equiv.Perm X) (s : X → A × A) (r : A)
    (hrec : ∀ x, (s x).2 = r) (hopen : ∀ m, 1 ≤ m → (e ^ m) o ≠ o) (t : ℕ) (ht : 1 ≤ t) :
    (run o e t s o).1 = r :=
  clean_supply o e s r t (fun _ _ _ => hrec _) (fun m hm _ => hopen m hm) t ht le_rfl

/-- The integer line is an open orbit. -/
theorem line_open (m : ℕ) (hm : 1 ≤ m) : ((Equiv.addRight (1 : ℤ)) ^ m) 0 ≠ 0 := by
  have h : ∀ n : ℕ, ((Equiv.addRight (1 : ℤ)) ^ n) 0 = n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ_apply, ih]; simp
  rw [h]; exact_mod_cast (by omega : m ≠ 0)

/-- **Lattice translations are open.** On a lattice `ℤᵈ` routed by translation along a nonzero
vector, as along a D₄ root, the backward stream never returns. -/
theorem translation_open {d : ℕ} (v : Fin d → ℤ) (hv : v ≠ 0) (o : Fin d → ℤ) (m : ℕ)
    (hm : 1 ≤ m) : ((Equiv.addRight v) ^ m) o ≠ o := by
  have h : ∀ n : ℕ, ((Equiv.addRight v) ^ n) o = o + n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ_apply, ih]; simp [add_smul, add_assoc]
  rw [h]
  intro he
  have hz : m • v = 0 := by simpa using he
  apply hv
  funext i
  have := congrFun hz i
  simp only [Pi.smul_apply, Pi.zero_apply] at this
  rcases mul_eq_zero.mp this with h0 | h0
  · omega
  · exact h0

/-- **Exact maintenance forever on the lattice.** With translation routing along a nonzero vector
and every record at the reference, the coupling site holds the reference at every tick. -/
theorem lattice_forever {d : ℕ} (v : Fin d → ℤ) (hv : v ≠ 0) (o : Fin d → ℤ) {A : Type*}
    (s : (Fin d → ℤ) → A × A) (r : A) (hrec : ∀ x, (s x).2 = r) (t : ℕ) (ht : 1 ≤ t) :
    (run o (Equiv.addRight v) t s o).1 = r :=
  open_orbit_forever o _ s r hrec (fun m hm => translation_open v hv o m hm) t ht

/-- **A closed ring returns the disturbance.** If the orbit of `o` closes after exactly `N ≥ 1`
steps, the live value that entered the site at tick `1` is back on the site's live output at tick
`N + 1`. Exact repair of arbitrary disturbances cannot last beyond one circuit. -/
theorem ring_returns (o : X) (e : Equiv.Perm X) (s : X → A × A) (N : ℕ) (hN : 1 ≤ N)
    (hclose : (e ^ N) o = o) (hmin : ∀ m, 1 ≤ m → m < N → (e ^ m) o ≠ o) :
    (run o e (N + 1) s o).1 = (s (e⁻¹ o)).1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [show n + 1 + 1 = (n + 1) + 1 by rfl, run_succ]
  simp only [step, ite_true]
  have h1 : run o e n (run o e 1 s) = run o e (n + 1) s := by rw [← run_add, add_comm]
  rw [← h1]
  have hp := record_path o e (run o e 1 s) n 1
    (fun j hj => hmin (1 + j) (by omega) (by omega))
  rw [pow_one] at hp
  rw [hp, add_comm 1 n, hclose]
  simp [run, step]

/-- On finite substrates this is Paper II's `NativeReferenceBackground.advance`. -/
theorem step_eq_advance [Fintype X] (o : X) (e : Equiv.Perm X) (s : X → A × A) :
    step o e s = NativeReferenceBackground.advance o e s := rfl

end PMAction.RecordSupply
