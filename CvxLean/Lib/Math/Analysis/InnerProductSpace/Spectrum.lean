import Mathlib.Analysis.Matrix.Spectrum

/-!
Version of the spectral theorem.
-/

namespace LinearMap

variable {𝕜 : Type _} [RCLike 𝕜]
variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)
variable {T : E →ₗ[𝕜] E}

/-- *Diagonalization theorem*, *spectral theorem*; version 3: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
lemma spectral_theorem' (v : E) (i : Fin n)
    (xs : OrthonormalBasis (Fin n) 𝕜 E) (as : Fin n → ℝ)
    (hxs : ∀ j, Module.End.HasEigenvector T (as j) (xs j)) :
    xs.repr (T v) i = as i * xs.repr v i := by
  suffices hsuff : ∀ (w : EuclideanSpace 𝕜 (Fin n)),
    T (xs.repr.symm w) = xs.repr.symm ((PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin n => 𝕜)).symm
      (fun i => (as i : 𝕜) * (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin n => 𝕜)) w i)) by
      simpa only [LinearIsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
        using congr_arg (fun (v : E) => (xs.repr) v i) (hsuff ((xs.repr) v))
  intros w
  simp_rw [← OrthonormalBasis.sum_repr_symm, map_sum, LinearMap.map_smul,
    fun j => Module.End.mem_eigenspace_iff.mp (hxs j).1, smul_smul]
  congr 1
  ext j
  simp only [PiLp.continuousLinearEquiv_symm_apply, PiLp.continuousLinearEquiv_apply]
  ring_nf

end LinearMap
