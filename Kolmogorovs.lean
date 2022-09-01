/-
James Gibson
Kolmogorov 0-1 law-/

import tactic
import measure_theory.measurable_space
import probability.independence

open  measure_theory.measure probability_theory  
open_locale classical measure_theory  ennreal big_operators  

namespace measure_theory 
namespace probability_theory 

variables {α : Type}

/--Construct the σ-algebra of sets, s, such that for each j satisfying n ≤ j ≤ n + k,
   the image under the function Fn j of the set s is measurable in the σ-algebra β j
   Denoted Fₙⁿ⁺ᵏ.--/
def Fnk_algebra (β : ℕ → Type) (fn : Π (n: ℕ), α → β n)
  (m : Π (n : ℕ), measurable_space (β n)) (n k : ℕ) : measurable_space α :=
/-Define the function from set α to Prop which is true when the set is in the σ-algebra-/
  { measurable_set' := λ (s : set α), ∀ (i ∈ finset.range (k + 1)), 
      ∃(s' : set (β (n + i))), (m (n + i)).measurable_set' s' ∧ fn (n + i) ⁻¹' s' = s,
  /-Show that ∅ is in the σ-algebra-/
    measurable_set_empty := 
      begin 
        intros i hi, use ∅,
        exact ⟨(m (n + i)).measurable_set_empty, rfl⟩ 
      end,
  /-Show the σ-algebra is closed under complements-/
    measurable_set_compl := 
      begin
      intros s h i hi, specialize h i hi, 
      choose s' hs' using h,
      use s'ᶜ,
      split,
        { exact (m (n + i)).measurable_set_compl _ hs'.1},
        { rw ← (hs'.2),
          simp only [set.preimage_compl]},
      end,
  /-Show the σ-algebra is closed under countable unions-/
    measurable_set_Union :=
      begin
        intros seq hyp j hjrange,
        have : ∀ (i : ℕ), (∃ (s' : set (β (n + j))), 
          (m (n + j)).measurable_set' s' ∧ fn (n + j) ⁻¹' s' = seq i),
        { intros i,
          exact hyp i j hjrange},
        choose seq' hseq' using this,
        use ⋃ (i : ℕ), seq' i,
        split,
        { exact (m (n + j)).measurable_set_Union (λ (i : ℕ), seq' i) (λ i, (hseq' i).1)},
        { simp only [hseq', set.preimage_Union]},
      end}

/--Define the σ-algebra generated from the union of σ-algebras 𝔽ₙⁿ⁺ᵏ for fixed n with k : ℕ.
   Denoted 𝔽ₙ--/
def Fn_σ_algebra (β : ℕ → Type) (m : Π (n : ℕ), measurable_space (β n))
  (fn : Π (n: ℕ), α → β n) (n : ℕ) : measurable_space α :=
  measurable_space.generate_from 
    {s : set α | ∃ (i : ℕ),  (Fnk_algebra β fn m n i).measurable_set' s}

/--Define the tail σ-algebra as the intersection of the σ-algebras 𝔽ₙ for n : ℕ.
   Denoted as τ.--/
def tail_σ_algebra (β : ℕ → Type) (fn : Π (n: ℕ), α → β n) (m : Π (n : ℕ), measurable_space (β n)) : 
  measurable_space α :=
  { measurable_set' := λ s, ∀ (n : ℕ), (Fn_σ_algebra β m fn n).measurable_set' s,
  /-Show the empty set is in this σ-algebra-/
  measurable_set_empty := 
    begin
      intro n,
      exact (Fn_σ_algebra β m fn n).measurable_set_empty,
    end,
  /-Show the σ-algebra is closed under complements-/
  measurable_set_compl := 
    begin
      intros s hyp n,
      exact (Fn_σ_algebra β m fn n).measurable_set_compl _ (hyp n),
    end,
  /-Show the σ-algebra is closed under countable unions-/
  measurable_set_Union := 
    begin
      intros seq hyp n,
      have : ∀ (i : ℕ), (Fn_σ_algebra β m fn n).measurable_set' (seq i),
        { intro i,  exact hyp i n},
      exact (Fn_σ_algebra β m fn n).measurable_set_Union _ this,
    end}

/--Define what it means for a σ-algebra, m, to be independent of a collection of sets
    i.e. each m measurable set is independent w.r.t. μ to each set in the collection--/
def indep_mspace_sets [measurable_space α] (μ : measure α) (m : measurable_space α) (col : set (set α)) : Prop :=
  ∀ s₁ s₂ : set α, m.measurable_set' s₁ → s₂ ∈ col → μ(s₁ ∩ s₂) = μ(s₁) * μ(s₂) 

/--For events in a σ-algebra which is independent with itself w.r.t. a probability measure μ,
   the probability of each event is either 0 or 1.--/
lemma self_Indep_result (m₁ : measurable_space α) [measurable_space α] 
  (μ : measure α) (hμ : is_probability_measure μ) (h : indep m₁ m₁ μ) : 
  ∀ (s : set α), m₁.measurable_set' s → μ s = 0 ∨ μ s = 1 :=
begin
  intros s hs,
  /-specialize independence to obtain that μ s = (μ s) ^ 2-/
  specialize h s s hs hs,
  rw s.inter_self at h,
  /-prove μ s < top so that we can use that μ s ≠ top later using a one line lemma-/
  have suppl : μ s < ⊤,
    { calc  μ s ≤ 1  : prob_le_one
            ... < ⊤  : ennreal.one_lt_top,  },
  have this1 : μ s - (μ s) * (μ s) = 0,
    { have : μ s - μ s = 0, 
      { norm_num [@ennreal.add_sub_self 0 (μ s) (lt_top_iff_ne_top.1 suppl)], },
      nth_rewrite 0 ← h,
      exact this, },
  /-factorise to a product of 2 things which equals 0-/
  have this2 : μ s * (1 - μ s) = μ s - (μ s) * (μ s),
  { sorry, },
  rw ← this2 at this1, clear this2,
  /-rearrange goal slightly-/
  suffices suff: μ s = 0 ∨ 1 - μ s = 0,
  { cases suff,
    { left,
      assumption, },
    { right,
      norm_num at suff,
      exact ge_antisymm suff prob_le_one, },  },
  apply zero_eq_mul.mp,
  exact eq.symm this1,
  exact canonically_ordered_comm_semiring.to_no_zero_divisors,
end

/--Proves that if a σ-algebra, m, is independent to a collection of measurable sets, col, then m is independent 
   to the σ-algebra generated by col, deonted σ(col) --/
lemma indep_of_gen_of_indep_mspace_sets [measurable_space α] (μ : measure α) (m : measurable_space α) 
  (col : set (set α)) (h : @indep_mspace_sets α _inst_1 μ m col) (h2: ∀ s ∈ col, _inst_1.measurable_set' s) : 
  @indep α m (measurable_space.generate_from col) _inst_1 μ :=
begin
  /-Introduce arbitrary sets s₁, s₂ in m and col respectively-/
  intros s₁ s₂ hs₁ hs₂,
  /-Work through the cases on the inductive type hs₂-/
  cases hs₂,
  /-Case s₂ is in col, follows from assumption-/
  { exact h s₁ s₂ hs₁ hs₂_H, },
  /-Case s₂ is the empty set, follows from measure of empty set-/
  { have : (λ (a : α), false) = (∅ : set α), by congr',
    rw this at *,
    rw [set.inter_empty s₁, measure_empty],
    ring, },
  /-Case s₂ is complement of σ(col) measurable set-/
  { have :  (λ (a : α), a ∉ hs₂_s) = hs₂_sᶜ, by congr',
    rw this at *, clear this,
    /-rw (@measure_compl α _inst_1 μ hs₂_s (h2 hs₂_s hs₂_ᾰ)  (sorry)),-/
    sorry,  },
  /-Case s₂ is union of σ(col) measurable sets-/
  { sorry,  },
end

/--Prove that if the functions fn are measurable w.r.t. (Ω, 𝔽, μ), then for any set, s, in the union
   ⋃ (i : ℕ), 𝔽ₙ₊₁ⁿ⁺¹⁺ⁱ, s is measurable w.r.t. 𝔽 --/
lemma measurable_prelim (β : ℕ → Type) (m : Π (n : ℕ), measurable_space (β n)) 
  (fn : Π (n: ℕ), α → β n) (k : ℕ) [measurable_space α] 
  (h2 : ∀ (i : ℕ), measurable (fn i)) :
  ∀ (s : set α), s ∈ {s : set α | ∃ (j : ℕ), (Fnk_algebra β fn m k j).measurable_set' s} → 
  _inst_1.measurable_set' s:=
begin
  /-Introduce a set s in ⋃ (i : ℕ), 𝔽ₙ₊₁ⁿ⁺¹⁺ⁱ-/
  intros s hs,
  /-Using hs, find k_1 s.t. s is measurable in 𝔽ₙⁿ⁺ᵏ-/
  choose k_1 hk using hs,
  /-Produce a function from i ≤ k_1 to a set over the type β (k + i)
    and a hyp stating this set is m (k + i) measurable its fn (k + i) preimage is s. -/
  choose l hl using hk,
  have : 0 ∈ finset.range (k_1 + 1), by  simp only [finset.mem_range, nat.succ_pos'],
  /-Use measurability of fn 0 and that the set fn 0 (s) is measurable to conclude s is measurable-/
  specialize hl 0 this,
  have this3 :  measurable_set (fn (k + 0) ⁻¹' l 0 this),
  { exact (@h2 (k + 0)) (l 0 this) hl.1, },
  rwa hl.2 at this3,
end

/--Proves that the σ-algebra 𝔽₀ⁿ is independent to the collection of sets ⋃ (i : ℕ), 𝔽ₙ₊₁ⁿ⁺¹⁺ⁱ   .--/
lemma F1nindep (β : ℕ → Type) (m : Π (n : ℕ), measurable_space (β n)) (fn : Π (n: ℕ), α → β n) (n : ℕ)
  [measurable_space α] (μ : measure α) 
  (hI : Indep_fun m fn μ) :
  indep_mspace_sets μ (Fnk_algebra β fn m 0 n) 
  {s : set α | ∃ (i : ℕ),  (Fnk_algebra β fn m (n + 1) i).measurable_set' s} :=
begin
  /-Take arbitrary sets s₁, s₂ in 𝔽₀ⁿ and ⋃ (i : ℕ), 𝔽ₙ₊₁ⁿ⁺¹⁺ⁱ respectively. 
    If we show these sets are independent we are done.-/
  intros s₁ s₂ hs₁ hs₂, 
  /-Select an j such that s₂ ∈ 𝔽ₙ₊₁ⁿ⁺¹⁺ʲ-/
  choose j hs₂' using hs₂,
  /-Using def of 𝔽ₙ₊₁ⁿ⁺¹⁺ʲ, find m (n + 1 + j) measurable set, s₂', satisfying the preimage
    under fn (n + 1 + j) of s₂' is s₂.-/
  specialize hs₂' j (finset.self_mem_range_succ j),
  choose s₂' hs₂'' using hs₂',
  /-Using def of 𝔽₀ⁿ, find m 0 measurable set s₁' satisfying the preimage
    under fn 0 is s₁.-/
  specialize hs₁ 0 (by simp only [finset.mem_range, nat.succ_pos']),
  choose s₁' hs₁' using hs₁,
  /-Have that the comap σ-algebras generated by (fn 0, m 0) and (fn (n + 1 + j), m (n + 1 + j))
    are independent from the independence of fn's.-/
  have comapindep : indep (measurable_space.comap (fn 0) (m 0)) (measurable_space.comap (fn (n + 1 + j)) (m (n + 1 + j))) μ,
  { exact Indep.indep hI (by linarith), },
  /-Prove s₁ is measurable in the comap σ-algebra of (fn 0, m 0) by using the m 0 measurability of 
    s₁' and that fn 0 ⁻¹ s' = s -/
  have h₁ : (measurable_space.comap (fn 0) (m 0)).measurable_set' s₁,
  { exact ⟨s₁', hs₁'⟩,  },
  /-Prove s₂ is measurable in the comap σ-algebra of (fn (n + 1 + j), m (n + 1 + j) using similar logic above-/
  have h₂ : (measurable_space.comap (fn (n + 1 + j)) (m (n + 1 + j))).measurable_set' s₂,
  { exact ⟨ s₂', hs₂''⟩,  },
  /-Use independence of the comap σ-algebras which s₁ and s₂ are in to conclude the goal.-/
  exact (comapindep s₁ s₂ h₁ h₂),
end

/--Prove the σ-algebra 𝔽₀ⁿ is independent to the σ-algebra 𝔽ₙ₊₁ w.r.t. μ given that the functions 
   are independent from each other w.r.t. μ--/
lemma F1nFnaddone_indep (β : ℕ → Type) (m : Π (n : ℕ), measurable_space (β n)) 
  (fn : Π (n: ℕ), α → β n) (n : ℕ) [measurable_space α] (μ : measure α) 
  (hI : Indep_fun m fn μ) (h2 : ∀ (n : ℕ), measurable (fn n)): 
  indep (Fnk_algebra β fn m 0 n) (Fn_σ_algebra β m fn (n + 1)) μ :=
begin
  exact indep_of_gen_of_indep_mspace_sets μ (Fnk_algebra β fn m 0 n) 
    {s : set α | ∃ (i : ℕ),  (Fnk_algebra β fn m (n + 1) i).measurable_set' s}
    (F1nindep β m fn n μ hI) 
    (measurable_prelim β m fn (n + 1) h2),
end

/--Prove the Kolmogorov 0-1 law, which states that one a probability space (Ω, 𝔽, μ),
   for independent measurable functions fn, any set in the tail σ-algebra generated by 
   the fn's must have probability either 1 or 0.--/
theorem Kolmogorov_0_1 (β : ℕ → Type) (m : Π (n : ℕ), measurable_space (β n)) 
  (fn : Π (n: ℕ), α → β n) [measurable_space α] (μ : measure α) (hμ : is_probability_measure μ)
  (hI : Indep_fun m fn μ) (h2 : ∀ (n : ℕ), measurable (fn n)) : 
  ∀ (s : set α), (tail_σ_algebra β fn m).measurable_set' s → μ s = 0 ∨ μ s = 1 :=
begin
  /-First show 𝔽₀ⁿ is independent to τ for all n-/
  have h₁ : ∀ (n : ℕ), indep (Fnk_algebra β fn m 0 n) (tail_σ_algebra β fn m) μ,
    /-Intro sets s₁ s₂ in 𝔽₀ⁿ, τ respectively for arbitrary n -/
  { intros n s₁ s₂ hs₁ hs₂,                   
    /-Sufficient that s₂ is 𝔽ₙ₊₁ measurable as we've already proven 𝔽₀ⁿ and 𝔽ₙ₊₁ are independent-/                          
    suffices : (Fn_σ_algebra β m fn (n + 1)).measurable_set' s₂,
    { exact (F1nFnaddone_indep β m fn n μ hI h2) s₁ s₂ hs₁ this, },
    exact hs₂ (n + 1), 
  },
  /-Second show τ and ⋃ n, 𝔽₀ⁿ are independent-/
  have h₂ : indep_mspace_sets μ (tail_σ_algebra β fn m)
    {s : set α | ∃ (n : ℕ), (Fnk_algebra β fn m 0 n).measurable_set' s},
    /-Intro sets s₁ s₂ in τ and ⋃ n, 𝔽₀ⁿ-/
  { intros s₁ s₂ hs₁ hs₂,
    /-Specify an n s.t. s₂ is 𝔽₀ⁿ measurable-/
    choose n hn using hs₂,
    /-result follows from 𝔽₀ⁿ, τ independence after rearranging-/
    have : μ (s₂ ∩ s₁) = μ s₂ * μ s₁, from h₁ n s₂ s₁ hn hs₁,
    rwa [set.inter_comm s₁ s₂, mul_comm (μ s₁) (μ s₂)], 
  },
  /-Third prove τ, 𝔽ₙ are independent-/
  have h₃ : indep (tail_σ_algebra β fn m) (Fn_σ_algebra β m fn 0) μ ,
  { exact (indep_of_gen_of_indep_mspace_sets μ (tail_σ_algebra β fn m)
      {s : set α | ∃ (n : ℕ), (Fnk_algebra β fn m 0 n).measurable_set' s} h₂
      (measurable_prelim β m fn 0 h2)), 
  },
  /-Finally show τ is independent with itself-/
  have h₄ : indep (tail_σ_algebra β fn m) (tail_σ_algebra β fn m) μ,
    /-Intros 2 sets in τ-/
  { intros s₁ s₂ hs₁ hs₂,
    /-Show its sufficient that s₂ is 𝔽₀ measurable using independence of 𝔽₀ and τ-/
    suffices : (Fn_σ_algebra β m fn 0).measurable_set' s₂,
      { exact h₃ s₁ s₂ hs₁ this, },
    /-Show s₂ is 𝔽₀ measruable using definition of τ-/
    exact hs₂ 0,
  },
  /-Use earlier self_indep_result to conclude since we now have that τ is self-independent-/
  exact self_Indep_result (tail_σ_algebra β fn m) μ hμ h₄,
end

end probability_theory
end measure_theory
#lint