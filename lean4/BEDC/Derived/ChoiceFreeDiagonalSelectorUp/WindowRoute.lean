import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ChoiceFreeDiagonalSelectorCarrier [AskSetup] [PackageSetup]
    (epsilon window stream readback realSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory epsilon ∧ UnaryHistory window ∧ UnaryHistory stream ∧
    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont epsilon window transport ∧ Cont stream readback replay ∧
          PkgSig bundle provenance pkg

theorem ChoiceFreeDiagonalSelectorCarrier_window_route [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName windowRead
      witnessRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont epsilon window windowRead →
        Cont windowRead stream witnessRead →
          Cont witnessRead readback sealRead →
            UnaryHistory windowRead ∧ UnaryHistory witnessRead ∧ UnaryHistory sealRead ∧
              Cont epsilon window windowRead ∧ Cont windowRead stream witnessRead ∧
                Cont witnessRead readback sealRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: ChoiceFreeDiagonalSelectorCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier epsilonWindow windowStream witnessReadback
  obtain ⟨epsilonUnary, windowUnary, streamUnary, readbackUnary, _realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary windowUnary epsilonWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowReadUnary streamUnary windowStream
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed witnessReadUnary readbackUnary witnessReadback
  exact
    ⟨windowReadUnary, witnessReadUnary, sealReadUnary, epsilonWindow, windowStream,
      witnessReadback, provenancePkg⟩

theorem ChoiceFreeDiagonalSelectorCarrier_ledger_obligation [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName ledgerRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont provenance localName ledgerRead →
        Cont ledgerRead replay namedRead →
          PkgSig bundle namedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row provenance ∨ hsame row localName ∨ hsame row replay ∨
                    hsame row ledgerRead ∨ hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont provenance localName ledgerRead ∧
                    Cont ledgerRead replay namedRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle namedRead pkg)
                hsame ∧
              UnaryHistory ledgerRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier provenanceLocal ledgerReplay namedPkg
  obtain ⟨_epsilonUnary, _windowUnary, _streamUnary, _readbackUnary, _realSealUnary,
    _transportUnary, replayUnary, provenanceUnary, localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceLocal
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary replayUnary ledgerReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row provenance ∨ hsame row localName ∨ hsame row replay ∨
              hsame row ledgerRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont provenance localName ledgerRead ∧
              Cont ledgerRead replay namedRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle namedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRead
          ⟨hsame_refl namedRead, namedUnary⟩
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
        right
        right
        right
        right
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenanceLocal, ledgerReplay, provenancePkg, namedPkg⟩
    }
  exact ⟨cert, ledgerUnary, namedUnary⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp
