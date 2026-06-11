import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# RegularCauchyDifferenceBoundUp finite carrier surface.
-/

namespace BEDC.Derived.RegularCauchyDifferenceBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyDifferenceBoundCarrier [AskSetup] [PackageSetup]
    (X Y W D E R H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X Y W ∧ Cont W D E ∧
        Cont E R H ∧ Cont H C N ∧ PkgSig bundle P pkg

theorem RegularCauchyDifferenceBoundCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X Y W D E R H C P N diffRead envelopeRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDifferenceBoundCarrier X Y W D E R H C P N bundle pkg →
      Cont W D diffRead →
        Cont diffRead E envelopeRead →
          Cont envelopeRead R sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row Y ∨ hsame row W ∨ hsame row D ∨
                      hsame row E ∨ hsame row R ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W D diffRead ∧
                      Cont diffRead E envelopeRead ∧ Cont envelopeRead R sealRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory diffRead ∧ UnaryHistory envelopeRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RegularCauchyDifferenceBoundCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowDyadicDiff diffEnvelope envelopeSeal sealPkg
  obtain ⟨_XUnary, _YUnary, WUnary, DUnary, EUnary, RUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _sourceWindow, _dyadicEnvelope, _sealTransport,
    _localReplay, provenancePkg⟩ := carrier
  have diffUnary : UnaryHistory diffRead :=
    unary_cont_closed WUnary DUnary windowDyadicDiff
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed diffUnary EUnary diffEnvelope
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed envelopeUnary RUnary envelopeSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row W ∨ hsame row D ∨ hsame row E ∨
              hsame row R ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D diffRead ∧ Cont diffRead E envelopeRead ∧
              Cont envelopeRead R sealRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowDyadicDiff, diffEnvelope, envelopeSeal, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, diffUnary, envelopeUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyDifferenceBoundUp
