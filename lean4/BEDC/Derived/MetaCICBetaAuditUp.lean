import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICBetaAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICBetaAuditCarrier
    (S V T F O H C P N reductionRead conversionRead obstructionRead : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory S ∧ UnaryHistory V ∧ UnaryHistory T ∧ UnaryHistory F ∧
    UnaryHistory O ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont S T reductionRead ∧ Cont V T conversionRead ∧
        Cont conversionRead O obstructionRead

theorem MetaCICBetaAudit_reduction_conversion_boundary
    {S V T F O H C P N reductionRead conversionRead obstructionRead : BHist} :
    MetaCICBetaAuditCarrier S V T F O H C P N
        reductionRead conversionRead obstructionRead →
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row F ∨
              hsame row O ∨ hsame row reductionRead ∨ hsame row conversionRead ∨
                hsame row obstructionRead)
          (fun row : BHist =>
            hsame row obstructionRead ∧ Cont S T reductionRead ∧
              Cont V T conversionRead ∧ Cont conversionRead O obstructionRead)
          hsame ∧
        Cont S T reductionRead ∧ Cont V T conversionRead ∧
          Cont conversionRead O obstructionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro carrier
  obtain ⟨sUnary, vUnary, tUnary, _fUnary, oUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, reductionRoute, conversionRoute, obstructionRoute⟩ := carrier
  have reductionUnary : UnaryHistory reductionRead :=
    unary_cont_closed sUnary tUnary reductionRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed vUnary tUnary conversionRoute
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed conversionUnary oUnary obstructionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row F ∨
              hsame row O ∨ hsame row reductionRead ∨ hsame row conversionRead ∨
                hsame row obstructionRead)
          (fun row : BHist =>
            hsame row obstructionRead ∧ Cont S T reductionRead ∧
              Cont V T conversionRead ∧ Cont conversionRead O obstructionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obstructionRead
        ⟨hsame_refl obstructionRead, obstructionUnary⟩
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
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, reductionRoute, conversionRoute, obstructionRoute⟩
  }
  exact ⟨cert, reductionRoute, conversionRoute, obstructionRoute⟩

theorem MetaCICBetaAuditNameCertObligations [AskSetup] [PackageSetup]
    {S V T F O H C P N reductionRead conversionRead rigidityRead subjectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory V →
        UnaryHistory T →
          UnaryHistory F →
            UnaryHistory O →
              UnaryHistory C →
                Cont S T reductionRead →
                  Cont V T conversionRead →
                    Cont conversionRead F rigidityRead →
                      Cont O C subjectRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row subjectRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row V ∨ hsame row T ∨
                                    hsame row F ∨ hsame row O ∨ hsame row subjectRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S T reductionRead ∧
                                    Cont V T conversionRead ∧
                                      Cont conversionRead F rigidityRead ∧
                                        Cont O C subjectRead ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory reductionRead ∧ UnaryHistory conversionRead ∧
                                UnaryHistory rigidityRead ∧ UnaryHistory subjectRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro unaryS unaryV unaryT unaryF unaryO unaryC reductionRoute conversionRoute
    rigidityRoute subjectRoute sourcePkg namePkg
  have reductionUnary : UnaryHistory reductionRead :=
    unary_cont_closed unaryS unaryT reductionRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed unaryV unaryT conversionRoute
  have rigidityUnary : UnaryHistory rigidityRead :=
    unary_cont_closed conversionUnary unaryF rigidityRoute
  have subjectUnary : UnaryHistory subjectRead :=
    unary_cont_closed unaryO unaryC subjectRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row subjectRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row V ∨ hsame row T ∨
              hsame row F ∨ hsame row O ∨ hsame row subjectRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S T reductionRead ∧
              Cont V T conversionRead ∧
                Cont conversionRead F rigidityRead ∧
                  Cont O C subjectRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro subjectRead
        ⟨hsame_refl subjectRead, subjectUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, reductionRoute, conversionRoute, rigidityRoute, subjectRoute,
          sourcePkg, namePkg⟩
  }
  exact ⟨cert, reductionUnary, conversionUnary, rigidityUnary, subjectUnary⟩

theorem MetaCICBetaAuditObligationClosurePackage [AskSetup] [PackageSetup]
    {S V T F O H C P N reductionRead conversionRead rigidityRead subjectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory V ->
        UnaryHistory T ->
          UnaryHistory F ->
            UnaryHistory O ->
              UnaryHistory C ->
                Cont S T reductionRead ->
                  Cont V T conversionRead ->
                    Cont conversionRead F rigidityRead ->
                      Cont O C subjectRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist =>
                                  (hsame row rigidityRead ∨ hsame row subjectRead) ∧
                                    UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row V ∨ hsame row T ∨
                                    hsame row F ∨ hsame row O ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row rigidityRead ∨ hsame row subjectRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S T reductionRead ∧
                                    Cont V T conversionRead ∧
                                      Cont conversionRead F rigidityRead ∧
                                        Cont O C subjectRead ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory reductionRead ∧ UnaryHistory conversionRead ∧
                                UnaryHistory rigidityRead ∧ UnaryHistory subjectRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro unaryS unaryV unaryT unaryF unaryO unaryC reductionRoute conversionRoute
    rigidityRoute subjectRoute provenance nameRow
  have reductionUnary : UnaryHistory reductionRead :=
    unary_cont_closed unaryS unaryT reductionRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed unaryV unaryT conversionRoute
  have rigidityUnary : UnaryHistory rigidityRead :=
    unary_cont_closed conversionUnary unaryF rigidityRoute
  have subjectUnary : UnaryHistory subjectRead :=
    unary_cont_closed unaryO unaryC subjectRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row rigidityRead ∨ hsame row subjectRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row F ∨
              hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row rigidityRead ∨ hsame row subjectRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S T reductionRead ∧ Cont V T conversionRead ∧
              Cont conversionRead F rigidityRead ∧ Cont O C subjectRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rigidityRead
        ⟨Or.inl (hsame_refl rigidityRead), rigidityUnary⟩
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
        intro row other sameRows source
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        cases source.left with
        | inl sameRigidity =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameRigidity), otherUnary⟩
        | inr sameSubject =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameSubject), otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRigidity =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inl sameRigidity
      | inr sameSubject =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inr sameSubject
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, reductionRoute, conversionRoute, rigidityRoute, subjectRoute,
          provenance, nameRow⟩
  }
  exact ⟨cert, reductionUnary, conversionUnary, rigidityUnary, subjectUnary⟩

end BEDC.Derived.MetaCICBetaAuditUp
