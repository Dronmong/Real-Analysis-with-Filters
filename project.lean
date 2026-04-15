import Mathlib

open Filter Topology
open Filter Metric


def frechetFilter : Filter ℕ :=
  Filter.cofinite

lemma frechet_tail_lemma (A : Set ℕ) :
  A ∈ frechetFilter ↔ ∃ a : ℕ, Set.Ici a ⊆ A :=by
  have h1 : A ∈ frechetFilter ↔ A ∈ (Filter.atTop : Filter ℕ) := by
    simp [frechetFilter, Nat.cofinite_eq_atTop]
  have h2 : A ∈ (Filter.atTop : Filter ℕ) ↔ ∃ N, ∀ n ≥ N, n ∈ A :=by
    exact (Filter.mem_atTop_sets)
  have h3 : (∃ N, ∀ n ≥ N, n ∈ A) ↔ ∃ N, Set.Ici N ⊆ A := by
    exact Eq.to_iff rfl
  exact (h1.trans h2).trans h3

lemma seq_filter_equiv
    (a : ℕ → ℝ) (L : ℝ) :
    (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε) ↔
    (∀ ε > (0 : ℝ), {n : ℕ | |a n - L| < ε} ∈ frechetFilter) :=by
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N, hN⟩
    have htail :
        ∃ N, Set.Ici N ⊆ {n : ℕ | |a n - L| < ε} := by
      refine ⟨N, ?_⟩
      intro n hn
      exact hN n hn
    exact (frechet_tail_lemma _).mpr htail
  ·
    intro h ε hε
    have h' :
    ∃ N, Set.Ici N ⊆ {n : ℕ | |a n - L| < ε} := by
      apply (frechet_tail_lemma _).mp
      exact h ε hε
    rcases h' with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    exact hN hn


theorem tendsto_const_seq (c : ℝ) :
    Tendsto (fun _ : ℕ => c) (atTop : Filter ℕ) (𝓝 c) := by
  refine (tendsto_def.mpr ?_)
  intro s hs
  have h': c∈s:=by
    exact mem_of_mem_nhds hs
  have hpre:(fun _ : ℕ => c)⁻¹'s=Set.univ :=by
    ext n
    simp[h']
  simp[hpre]



example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by
    refine (tendsto_def.mpr ?_)
    intro s hs
    have hf' := tendsto_def.mp hf
    have hg' := tendsto_def.mp hg
    have hG : g ⁻¹' s ∈ G := hg' s hs
    have hF : f ⁻¹' (g ⁻¹' s) ∈ F := hf' _ hG
    simpa [Set.preimage, Function.comp] using hF


-- ε–δ definition of continuity at a point x₀ for f : ℝ → ℝ
def cont_eps_delta (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ {x : ℝ}, dist x x₀ < δ → dist (f x) (f x₀) < ε

theorem cont_filter_equiv (f : ℝ → ℝ) (x₀ : ℝ) :
  ContinuousAt f x₀ ↔ cont_eps_delta f x₀ := by
  simpa [cont_eps_delta] using
    (Metric.continuousAt_iff (f := f) : ContinuousAt f x₀ ↔ _)

theorem continuousAt_add
    (f g : ℝ → ℝ) (x : ℝ)
    (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun y => f y + g y) x := by
  let h : ℝ → ℝ × ℝ := fun y => (f y, g y)
  let k : ℝ × ℝ → ℝ := fun p => p.1 + p.2
  have h_pair : ContinuousAt h x := by
    simpa [h] using hf.prodMk hg
  have h_add : ContinuousAt k (h x) := by
    have hk : Continuous k := by
      simpa [k] using
        (continuous_fst.add continuous_snd :
          Continuous fun p : ℝ × ℝ => p.1 + p.2)
    simpa [h] using hk.continuousAt (x := h x)
  have h_comp : ContinuousAt (fun y => k (h y)) x :=
    ContinuousAt.comp' (f := h) (g := k) (x := x) h_add h_pair
  simpa [h, k] using h_comp


theorem continuousAt_of_hasDerivAt
    (f : ℝ → ℝ) (x f' : ℝ)
    (hf : HasDerivAt f f' x) :
    ContinuousAt f x := by
  have hdiff : DifferentiableAt ℝ f x := hf.differentiableAt
  rcases hdiff with ⟨L, hL⟩
  exact hL.continuousAt
