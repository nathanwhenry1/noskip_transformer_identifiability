import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Gauge

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Relabeling and the input-gauged tail

The finite relabeling operations are the neutral bookkeeping used by peeling.
The no-skip-specific addition is `inputGaugeTail`: it changes only the first
layer of a nonempty tail so evaluating the new tail at `Y` equals evaluating
the old tail at `G.matrix * Y`.
-/

noncomputable section

/-! ## Canonical first-layer relabeling -/

/-- Relabel only the first layer by a target-to-source head permutation. -/
def relabelFirstLayer {m k d : Nat} (theta : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) : Params (m + 1) k d :=
  fun l h => if l = 0 then theta 0 (sigma h) else theta l h

@[simp] theorem relabelFirstLayer_zero {m k d : Nat}
    (theta : Params (m + 1) k d) (sigma : Equiv.Perm (Fin k)) (h : Fin k) :
    relabelFirstLayer theta sigma 0 h = theta 0 (sigma h) := by
  simp [relabelFirstLayer]

@[simp] theorem relabelFirstLayer_succ {m k d : Nat}
    (theta : Params (m + 1) k d) (sigma : Equiv.Perm (Fin k))
    (l : Fin m) (h : Fin k) :
    relabelFirstLayer theta sigma l.succ h = theta l.succ h := by
  simp [relabelFirstLayer]

/-- Deleting the first layer erases a first-layer relabeling. -/
@[simp] theorem relabelFirstLayer_tail {m k d : Nat}
    (theta : Params (m + 1) k d) (sigma : Equiv.Perm (Fin k)) :
    Fin.tail (relabelFirstLayer theta sigma) = Fin.tail theta := by
  funext l h
  simp [Fin.tail]

/-! ## Prepending a layer permutation -/

/-- Prepend the first-layer permutation to a tail permutation tuple. -/
def consLayerPerm {m k : Nat} (sigma0 : Equiv.Perm (Fin k))
    (tailSigma : Fin m → Equiv.Perm (Fin k)) :
    Fin (m + 1) → Equiv.Perm (Fin k) :=
  Fin.cases sigma0 tailSigma

@[simp] theorem consLayerPerm_zero {m k : Nat}
    (sigma0 : Equiv.Perm (Fin k))
    (tailSigma : Fin m → Equiv.Perm (Fin k)) :
    consLayerPerm sigma0 tailSigma 0 = sigma0 :=
  rfl

@[simp] theorem consLayerPerm_succ {m k : Nat}
    (sigma0 : Equiv.Perm (Fin k))
    (tailSigma : Fin m → Equiv.Perm (Fin k)) (l : Fin m) :
    consLayerPerm sigma0 tailSigma l.succ = tailSigma l :=
  rfl

/-! ## Input-gauged target tails -/

/-- Interface chain with input gauge `G⁻¹` and every later interface equal to
the identity.  It is defined only for a nonempty depth `n + 1`. -/
def inputGaugeInterfaces (n d : Nat) (G : GaugeMatrix d) :
    InterfaceGaugeChain (n + 1) d :=
  Fin.cases G⁻¹ (fun _ => 1)

@[simp] theorem inputGaugeInterfaces_zero {n d : Nat} (G : GaugeMatrix d) :
    inputGaugeInterfaces n d G 0 = G⁻¹ :=
  rfl

@[simp] theorem inputGaugeInterfaces_succ {n d : Nat} (G : GaugeMatrix d)
    (i : Fin (n + 1)) :
    inputGaugeInterfaces n d G i.succ = 1 :=
  rfl

/-- The input-gauged form of a nonempty target tail.  Its first-layer heads are
`(V G, Gᵀ A G)` in the internal `(V,A)` parameter ordering, and deeper layers
are unchanged. -/
def inputGaugeTail {n k d : Nat} (G : GaugeMatrix d)
    (psi : Params (n + 1) k d) : Params (n + 1) k d :=
  gaugeAction (inputGaugeInterfaces n d G) psi

@[simp] theorem valueMatrix_inputGaugeTail_zero {n k d : Nat}
    (G : GaugeMatrix d) (psi : Params (n + 1) k d) (a : Fin k) :
    valueMatrix (inputGaugeTail G psi) 0 a =
      valueMatrix psi 0 a * G.matrix := by
  rw [inputGaugeTail, valueMatrix_gaugeAction]
  change
    (inputGaugeInterfaces n d G (0 : Fin (n + 1)).succ).matrix *
          valueMatrix psi 0 a *
          (inputGaugeInterfaces n d G 0).invMatrix =
      valueMatrix psi 0 a * G.matrix
  rw [inputGaugeInterfaces_succ, inputGaugeInterfaces_zero,
    GaugeMatrix.invMatrix_inv]
  simp

@[simp] theorem attentionMatrix_inputGaugeTail_zero {n k d : Nat}
    (G : GaugeMatrix d) (psi : Params (n + 1) k d) (a : Fin k) :
    attentionMatrix (inputGaugeTail G psi) 0 a =
      G.matrixᵀ * attentionMatrix psi 0 a * G.matrix := by
  rw [inputGaugeTail, attentionMatrix_gaugeAction]
  change
    (inputGaugeInterfaces n d G 0).invTranspose *
          attentionMatrix psi 0 a *
          (inputGaugeInterfaces n d G 0).invMatrix =
      G.matrixᵀ * attentionMatrix psi 0 a * G.matrix
  rw [inputGaugeInterfaces_zero, GaugeMatrix.invTranspose,
    GaugeMatrix.invMatrix_inv]

@[simp] theorem inputGaugeTail_succ {n k d : Nat}
    (G : GaugeMatrix d) (psi : Params (n + 1) k d)
    (l : Fin n) (a : Fin k) :
    inputGaugeTail G psi l.succ a = psi l.succ a := by
  apply Prod.ext
  · change valueMatrix (inputGaugeTail G psi) l.succ a = valueMatrix psi l.succ a
    rw [inputGaugeTail, valueMatrix_gaugeAction]
    rw [Fin.castSucc_succ, inputGaugeInterfaces_succ,
      inputGaugeInterfaces_succ]
    simp
  · change attentionMatrix (inputGaugeTail G psi) l.succ a =
      attentionMatrix psi l.succ a
    rw [inputGaugeTail, attentionMatrix_gaugeAction]
    rw [Fin.castSucc_succ, inputGaugeInterfaces_succ]
    simp [GaugeMatrix.invTranspose]

/-- TeX `eq:input-gauge-identity`, in the orientation used by peeling. -/
theorem transformer_inputGaugeTail {n k d T : Nat}
    (G : GaugeMatrix d) (psi : Params (n + 1) k d)
    (Y : Matrix (Fin d) (Fin T) Real) :
    transformer (inputGaugeTail G psi) Y =
      transformer psi (G.matrix * Y) := by
  let H := inputGaugeInterfaces n d G
  have h := transformer_gaugeAction H psi
    (G.matrix * Y)
  have hinput : (H 0).matrix * (G.matrix * Y) = Y := by
    change G.invMatrix * (G.matrix * Y) = Y
    rw [← Matrix.mul_assoc, GaugeMatrix.invMatrix_mul_matrix]
    simp
  have hlast : (H (Fin.last (n + 1))).matrix = 1 := by
    have hindex : Fin.last (n + 1) = (Fin.last n).succ := by
      ext
      simp
    rw [hindex]
    change (inputGaugeInterfaces n d G (Fin.last n).succ).matrix = 1
    rw [inputGaugeInterfaces_succ]
    rfl
  change transformer (gaugeAction H psi) Y = transformer psi (G.matrix * Y)
  calc
    transformer (gaugeAction H psi) Y =
        transformer (gaugeAction H psi) ((H 0).matrix * (G.matrix * Y)) := by
      rw [hinput]
    _ = (H (Fin.last (n + 1))).matrix * transformer psi (G.matrix * Y) := h
    _ = transformer psi (G.matrix * Y) := by rw [hlast]; simp

end

end TransformerIdentifiability.NLayer.NoSkip
