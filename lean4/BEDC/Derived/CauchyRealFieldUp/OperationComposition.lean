import BEDC.Derived.CauchyRealFieldUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRealFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyRealFieldCarrier_operation_composition
    {R S D Z A M I O H C P N addRead mulRead recipGate recipRead : BHist} :
    UnaryHistory R →
      UnaryHistory S →
        UnaryHistory D →
          UnaryHistory A →
            UnaryHistory M →
              UnaryHistory O →
                UnaryHistory I →
                  Cont R S addRead →
                    Cont addRead D mulRead →
                      Cont O I recipGate →
                        Cont recipGate D recipRead →
                          cauchyRealFieldFields
                              (CauchyRealFieldUp.mk R S D Z A M I O H C P N) =
                            [R, S, D, Z, A, M, I, O, H, C, P, N] ∧
                            UnaryHistory addRead ∧ UnaryHistory mulRead ∧
                              UnaryHistory recipGate ∧ UnaryHistory recipRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro regularUnary streamUnary dyadicUnary _addUnary _mulUnary orderUnary reciprocalUnary
    addRoute mulRoute reciprocalGate reciprocalRoute
  have addReadUnary : UnaryHistory addRead :=
    unary_cont_closed regularUnary streamUnary addRoute
  have mulReadUnary : UnaryHistory mulRead :=
    unary_cont_closed addReadUnary dyadicUnary mulRoute
  have recipGateUnary : UnaryHistory recipGate :=
    unary_cont_closed orderUnary reciprocalUnary reciprocalGate
  have recipReadUnary : UnaryHistory recipRead :=
    unary_cont_closed recipGateUnary dyadicUnary reciprocalRoute
  exact ⟨rfl, addReadUnary, mulReadUnary, recipGateUnary, recipReadUnary⟩

def CauchyRealFieldCarrier [AskSetup] [PackageSetup]
    (regseq stream dyadic realSeal add product reciprocal order transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regseq ∧
    UnaryHistory stream ∧
      UnaryHistory dyadic ∧
        UnaryHistory realSeal ∧
          UnaryHistory add ∧
            UnaryHistory product ∧
              UnaryHistory reciprocal ∧
                UnaryHistory order ∧
                  UnaryHistory transport ∧
                    UnaryHistory replay ∧ UnaryHistory provenance ∧
                      UnaryHistory localName ∧ PkgSig bundle provenance pkg

theorem CauchyRealFieldRealCompletionConsumerBoundary [AskSetup] [PackageSetup]
    {regseq stream dyadic realSeal add product reciprocal order transport replay provenance
      localName fieldRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRealFieldCarrier regseq stream dyadic realSeal add product reciprocal order transport
        replay provenance localName bundle pkg →
      Cont replay realSeal fieldRead →
        Cont fieldRead dyadic completionRead →
          PkgSig bundle completionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row regseq ∨ hsame row stream ∨ hsame row dyadic ∨
                    hsame row realSeal ∨ hsame row add ∨ hsame row product ∨
                      hsame row reciprocal ∨ hsame row order ∨ hsame row completionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory fieldRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: CauchyRealFieldUp BHist Cont ProbeBundle Pkg PkgSig hsame
  -- BEDC touchpoint anchor: SemanticNameCert UnaryHistory
  intro carrier fieldRoute completionRoute completionPkg
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have realSealUnary : UnaryHistory realSeal := carrier.right.right.right.left
  have replayUnary : UnaryHistory replay :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  have fieldUnary : UnaryHistory fieldRead :=
    unary_cont_closed replayUnary realSealUnary fieldRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed fieldUnary dyadicUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regseq ∨ hsame row stream ∨ hsame row dyadic ∨
              hsame row realSeal ∨ hsame row add ∨ hsame row product ∨
                hsame row reciprocal ∨ hsame row order ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg)
          hsame := by
    refine
      { core :=
          { carrier_inhabited := ?_
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · exact ⟨completionRead, hsame_refl completionRead, completionUnary⟩
    · intro row _source
      exact hsame_refl row
    · intro row other same
      exact hsame_symm same
    · intro row middle other leftSame rightSame
      exact hsame_trans leftSame rightSame
    · intro row other same source
      exact
        ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    · intro row source
      exact
        Or.inr
          (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    · intro row source
      exact ⟨source.right, provenancePkg, completionPkg⟩
  exact ⟨cert, fieldUnary, completionUnary⟩

end BEDC.Derived.CauchyRealFieldUp
