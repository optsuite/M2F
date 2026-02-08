import Mathlib

open Subgroup

section

variable {G : Type} [Group G]

variable {H K : Subgroup G}

/-- If `H` is normal in `G`, then commutators with an element of `H` lie in `H`. -/
lemma commutator_mem_H_of_normal [H.Normal] {h g : G} (hh : h ∈ H) :
    h * g * h⁻¹ * g⁻¹ ∈ H := by
  have hg : g * h * g⁻¹ ∈ H := (inferInstance : H.Normal).conj_mem h hh g
  have hcomm : g * h * g⁻¹ * h⁻¹ ∈ H := by
    simpa [mul_assoc] using H.mul_mem hg (H.inv_mem hh)
  have hinv : (g * h * g⁻¹ * h⁻¹)⁻¹ ∈ H := H.inv_mem hcomm
  simpa [mul_assoc] using hinv

variable (H K)

/-- If `K` is normal in `H` (as a subgroup of `H`) and `K ≤ H`, then conjugating an element of `K`
by an element of `H` stays in `K` (as a subgroup of `G`). -/
lemma conj_mem_K_of_mem_H (h1 : K ≤ H) [(K.subgroupOf H).Normal] {h k : G}
    (hh : h ∈ H) (hk : k ∈ K) : h * k * h⁻¹ ∈ K := by
  have hkH : (⟨k, h1 hk⟩ : H) ∈ K.subgroupOf H := by
    -- `K.subgroupOf H` is the preimage of `K` under the inclusion `H → G`.
    simpa [Subgroup.mem_subgroupOf] using hk
  have hconj :
      (⟨h, hh⟩ : H) * (⟨k, h1 hk⟩ : H) * (⟨h, hh⟩ : H)⁻¹ ∈ K.subgroupOf H :=
    (inferInstance : (K.subgroupOf H).Normal).conj_mem _ hkH _
  -- Translate the membership statement back to `G`.
  have : (((⟨h, hh⟩ : H) * (⟨k, h1 hk⟩ : H) * (⟨h, hh⟩ : H)⁻¹ : H) : G) ∈ K :=
    (Subgroup.mem_subgroupOf).1 hconj
  simpa [mul_assoc] using this

/-- If `x` centralizes `K`, then any conjugate of `x` by an element of `H` also centralizes `K`,
assuming `K` is normal in `H`. -/
lemma conj_mem_centralizer_of_mem_centralizer (h1 : K ≤ H) [(K.subgroupOf H).Normal]
    {h x : G} (hh : h ∈ H) (hx : x ∈ Subgroup.centralizer (K : Set G)) :
    h * x * h⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro k hk
  have hk' : h⁻¹ * k * h ∈ K := by
    have hh' : h⁻¹ ∈ H := H.inv_mem hh
    -- conjugation of `k` by `h⁻¹` stays in `K`
    simpa using (conj_mem_K_of_mem_H (H := H) (K := K) h1 hh' hk)
  have hx' : (h⁻¹ * k * h) * x = x * (h⁻¹ * k * h) := hx _ hk'
  calc
    k * (h * x * h⁻¹) = h * ((h⁻¹ * k * h) * x) * h⁻¹ := by
      simp [mul_assoc]
    _ = h * (x * (h⁻¹ * k * h)) * h⁻¹ := by
      simpa [mul_assoc] using congrArg (fun t => h * t * h⁻¹) hx'
    _ = h * x * h⁻¹ * k := by
      simp [mul_assoc]
    _ = (h * x * h⁻¹) * k := by
      simp [mul_assoc]

/-- If `c ∈ H` and `c` centralizes `K` in `G`, then `c` (as an element of `H`) centralizes
`K.subgroupOf H`. -/
lemma subtype_mem_centralizer_subgroupOf_of_mem {c : G} (hcH : c ∈ H)
    (hc : c ∈ Subgroup.centralizer (K : Set G)) :
    (⟨c, hcH⟩ : H) ∈ Subgroup.centralizer (K.subgroupOf H) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  apply Subtype.ext
  have hkG : (k : G) ∈ K := (Subgroup.mem_subgroupOf).1 hk
  exact (Subgroup.mem_centralizer_iff.1 hc) (k : G) hkG

end

/- Let $G$ be a group and let $K\subseteq H$ be subgroups of $G$ with $K \lhd H$.
	If $H \lhd G$ and $C_H(K)=1$, prove that $H$ centralizes $C_G(K)$.-/
theorem le_centralizer_centralizer_of_centralizer_eq_bot {G : Type} [Group G] (H K : Subgroup G)
    [H.Normal] (h1 : K ≤ H) [(K.subgroupOf H).Normal]
    (h2 : Subgroup.centralizer (K.subgroupOf H) = (⊥ : Subgroup H)) :
    H ≤ Subgroup.centralizer (Subgroup.centralizer (K : Set G) : Set G) := by
  intro h hh
  -- Expand the target centralizer condition: `h` commutes with every `x ∈ C_G(K)`.
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  -- Consider the commutator `c = h * x * h⁻¹ * x⁻¹`.
  set c : G := h * x * h⁻¹ * x⁻¹
  have hcH : c ∈ H := by
    simpa [c] using (commutator_mem_H_of_normal (H := H) hh (g := x))
  have hx_conj : h * x * h⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
    conj_mem_centralizer_of_mem_centralizer (H := H) (K := K) h1 hh hx
  have hcC : c ∈ Subgroup.centralizer (K : Set G) := by
    have hx_inv : x⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.centralizer (K : Set G)).inv_mem hx
    have : (h * x * h⁻¹) * x⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.centralizer (K : Set G)).mul_mem hx_conj hx_inv
    simpa [c, mul_assoc] using this
  have hcCH : (⟨c, hcH⟩ : H) ∈ Subgroup.centralizer (K.subgroupOf H) :=
    subtype_mem_centralizer_subgroupOf_of_mem (H := H) (K := K) hcH hcC
  have hcEq1H : (⟨c, hcH⟩ : H) = 1 := by
    have : (⟨c, hcH⟩ : H) ∈ (⊥ : Subgroup H) := by
      simpa [h2] using hcCH
    simpa using this
  have hcEq1 : c = 1 := congrArg Subtype.val hcEq1H
  have hcEq1' : h * x * h⁻¹ * x⁻¹ = 1 := by
    simpa [c] using hcEq1
  have hx1 : h * x * h⁻¹ = x := by
    have := congrArg (fun t => t * x) hcEq1'
    simpa [mul_assoc] using this
  have hx2 : h * x = x * h := by
    have := congrArg (fun t => t * h) hx1
    simpa [mul_assoc] using this
  simpa using hx2.symm
