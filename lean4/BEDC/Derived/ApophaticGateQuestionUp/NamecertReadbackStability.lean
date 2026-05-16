import BEDC.Derived.ApophaticGateQuestionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_namecert_readback_stability [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback nameRow nameRead →
        PkgSig bundle nameRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row nameRow ∧
                  ApophaticGateQuestionCarrier socket question refusal readback transport route
                    provenance nameRow bundle pkg)
              (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont socket question readback ∧ hsame readback (append socket question) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle nameRead pkg)
              hsame ∧
            UnaryHistory nameRow ∧ UnaryHistory nameRead ∧
              Cont readback nameRow nameRead ∧ PkgSig bundle nameRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readbackNameRoute nameReadPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed readbackUnary nameRowUnary readbackNameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row nameRow ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket question readback ∧ hsame readback (append socket question) ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameRow ⟨hsame_refl nameRow, carrierPacket⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, unary_transport nameRowUnary (hsame_symm source.left)⟩
      ledger_sound := by
        intro _row _source
        exact
          ⟨socketQuestionReadback, readbackSameSourceQuestion, provenancePkg, nameReadPkg⟩
    }
  exact ⟨cert, nameRowUnary, nameReadUnary, readbackNameRoute, nameReadPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
