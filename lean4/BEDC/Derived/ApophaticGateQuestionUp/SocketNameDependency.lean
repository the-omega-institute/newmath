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

theorem ApophaticGateQuestionCarrier_socket_name_dependency [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow socketRead
      questionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont socket question socketRead →
        Cont socketRead readback questionRead →
          PkgSig bundle questionRead pkg →
            UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory readback ∧
              UnaryHistory socketRead ∧ UnaryHistory questionRead ∧
                Cont socket question socketRead ∧ Cont socketRead readback questionRead ∧
                  hsame readback (append socket question) ∧ PkgSig bundle questionRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row questionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        Cont socket question socketRead ∧ Cont socketRead readback row)
                      (fun row : BHist =>
                        hsame row questionRead ∧ PkgSig bundle questionRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketQuestionRead socketReadReadback questionReadPkg
  obtain ⟨socketUnary, questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, _provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary questionUnary socketQuestionRead
  have questionReadUnary : UnaryHistory questionRead :=
    unary_cont_closed socketReadUnary readbackUnary socketReadReadback
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row questionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          Cont socket question socketRead ∧ Cont socketRead readback row)
        (fun row : BHist =>
          hsame row questionRead ∧ PkgSig bundle questionRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro questionRead ⟨hsame_refl questionRead, questionReadUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro row source
        cases source.left
        exact ⟨socketQuestionRead, socketReadReadback⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, questionReadPkg⟩
    }
  exact
    ⟨socketUnary, questionUnary, readbackUnary, socketReadUnary, questionReadUnary,
      socketQuestionRead, socketReadReadback, readbackSameSourceQuestion, questionReadPkg,
      cert⟩

end BEDC.Derived.ApophaticGateQuestionUp
