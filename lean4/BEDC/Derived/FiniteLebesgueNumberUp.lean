import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.Derived.FiniteLebesgueNumberUp.RootRoutes
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusConsumerDeterminacy
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusWindowAdmission

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactRadiusSourceAccountability [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        PkgSig bundle compactRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row radius ∨ hsame row mesh ∨ hsame row compactRead)
              (fun row : BHist =>
                hsame row compactRead ∧ PkgSig bundle compactRead pkg ∧
                  Cont radius mesh compactRead)
              hsame ∧
            UnaryHistory radius ∧ UnaryHistory mesh ∧ UnaryHistory compactRead ∧
              Cont radius mesh compactRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier radiusMeshCompact compactPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have sourceCompact :
      (fun row : BHist => hsame row compactRead ∧ UnaryHistory row) compactRead := by
    exact ⟨hsame_refl compactRead, compactUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row radius ∨ hsame row mesh ∨ hsame row compactRead)
          (fun row : BHist =>
            hsame row compactRead ∧ PkgSig bundle compactRead pkg ∧
              Cont radius mesh compactRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro compactRead sourceCompact
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.left, compactPkg, radiusMeshCompact⟩
    }
  exact ⟨cert, radiusUnary, meshUnary, compactUnary, radiusMeshCompact, provenancePkg, compactPkg⟩

theorem FiniteLebesgueNumberL10ConsumerReadbackExactness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead compactRead
      continuousRead uniformRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow auditRead ->
        Cont auditRead radius phaseRead ->
          Cont phaseRead mesh compactRead ->
            Cont compactRead route continuousRead ->
              Cont continuousRead nameRow uniformRead ->
                Cont uniformRead provenance terminalRead ->
                  PkgSig bundle terminalRead pkg ->
                    UnaryHistory auditRead ∧ UnaryHistory phaseRead ∧
                      UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                        UnaryHistory uniformRead ∧ UnaryHistory terminalRead ∧
                          Cont route nameRow auditRead ∧ Cont auditRead radius phaseRead ∧
                            Cont phaseRead mesh compactRead ∧
                              Cont compactRead route continuousRead ∧
                                Cont continuousRead nameRow uniformRead ∧
                                  Cont uniformRead provenance terminalRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameAudit auditRadiusPhase phaseMeshCompact compactRouteContinuous
    continuousNameUniform uniformProvenanceTerminal terminalPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed auditUnary radiusUnary auditRadiusPhase
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed phaseUnary meshUnary phaseMeshCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed uniformUnary provenanceUnary uniformProvenanceTerminal
  exact
    ⟨auditUnary, phaseUnary, compactUnary, continuousUnary, uniformUnary, terminalUnary,
      routeNameAudit, auditRadiusPhase, phaseMeshCompact, compactRouteContinuous,
      continuousNameUniform, uniformProvenanceTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
