import BEDC.Derived.LawlessSequenceUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {window digit index transport replay provenance name digitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier
        window digit index transport replay provenance name bundle pkg →
      Cont window digit digitRead →
        PkgSig bundle digitRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row digitRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row window ∨ hsame row digit ∨ hsame row index ∨
                  hsame row digitRead)
              (fun row : BHist => hsame row digitRead ∧ PkgSig bundle digitRead pkg)
              hsame ∧
            UnaryHistory window ∧ UnaryHistory digit ∧ UnaryHistory index ∧
              UnaryHistory digitRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier windowDigitRead digitReadPkg
  obtain ⟨windowUnary, digitUnary, indexUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _provenancePkg, _namePkg⟩ := carrier
  have digitReadUnary : UnaryHistory digitRead :=
    unary_cont_closed windowUnary digitUnary windowDigitRead
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro digitRead ⟨hsame_refl digitRead, digitReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, digitReadPkg⟩
    }
  · exact ⟨windowUnary, digitUnary, indexUnary, digitReadUnary⟩

end BEDC.Derived.LawlessSequenceUp
