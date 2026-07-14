import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Core
import AnyLayerIdentifiabilityProof.NLayer.KHead.Permutation
import AnyLayerIdentifiabilityProof.NLayer.KHead.Matching
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.WindowAvoidance
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidLaurent
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.PoleArcs
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Trichotomy

/-!
This compile-only co-import test validates that the selected neutral KHead
modules coexist with the no-skip namespace.  It is not a library import.
-/

namespace TransformerIdentifiability.NLayer.NoSkip

#check KHead.unique_attention_permutation
#check KHead.global_labeling
#check KHead.TrichotomyLabel
#check collapseMatrix_sub_valueSum

end TransformerIdentifiability.NLayer.NoSkip
