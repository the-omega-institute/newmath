import BEDC.Derived.SupportNerveCensusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SupportNerveCensusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SupportNerveCensusCarrier [AskSetup] [PackageSetup]
    (support family nerve betti top lifted transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: SupportNerveCensusUp BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory support ∧ UnaryHistory family ∧ UnaryHistory nerve ∧ UnaryHistory betti ∧
    UnaryHistory top ∧ UnaryHistory lifted ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle localName pkg

theorem SupportNerveCensusNameCertObligations [AskSetup] [PackageSetup]
    {support family nerve betti top lifted transport replay provenance localName nerveRead
      bettiRead liftedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SupportNerveCensusCarrier support family nerve betti top lifted transport replay provenance
        localName bundle pkg →
      Cont support family nerveRead →
        Cont nerveRead betti bettiRead →
          Cont bettiRead lifted liftedRead →
            PkgSig bundle liftedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row liftedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row support ∨ hsame row family ∨ hsame row nerve ∨
                      hsame row betti ∨ hsame row top ∨ hsame row lifted ∨
                        hsame row liftedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont support family nerveRead ∧
                      Cont nerveRead betti bettiRead ∧ Cont bettiRead lifted liftedRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle liftedRead pkg)
                  hsame ∧
                UnaryHistory nerveRead ∧ UnaryHistory bettiRead ∧ UnaryHistory liftedRead := by
  -- BEDC touchpoint anchor: SupportNerveCensusCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier supportFamilyRoute nerveBettiRoute bettiLiftedRoute liftedPkg
  rcases carrier with
    ⟨supportUnary, familyUnary, _nerveUnary, bettiUnary, _topUnary, liftedUnary,
      _transportUnary, _replayUnary, provenanceUnary, _localNameUnary, provenancePkg,
      _localNamePkg⟩
  have nerveReadUnary : UnaryHistory nerveRead :=
    unary_cont_closed supportUnary familyUnary supportFamilyRoute
  have bettiReadUnary : UnaryHistory bettiRead :=
    unary_cont_closed nerveReadUnary bettiUnary nerveBettiRoute
  have liftedReadUnary : UnaryHistory liftedRead :=
    unary_cont_closed bettiReadUnary liftedUnary bettiLiftedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row liftedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row support ∨ hsame row family ∨ hsame row nerve ∨ hsame row betti ∨
              hsame row top ∨ hsame row lifted ∨ hsame row liftedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont support family nerveRead ∧
              Cont nerveRead betti bettiRead ∧ Cont bettiRead lifted liftedRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle liftedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro liftedRead ⟨hsame_refl liftedRead, liftedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, supportFamilyRoute, nerveBettiRoute, bettiLiftedRoute,
          provenancePkg, liftedPkg⟩
  }
  exact ⟨cert, nerveReadUnary, bettiReadUnary, liftedReadUnary⟩

end BEDC.Derived.SupportNerveCensusUp
