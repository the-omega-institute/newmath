import BEDC.Derived.RegularCauchyTailScheduleUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailSchedule_obligation_closure_package [AskSetup] [PackageSetup]
    {precision source window dyadic cofinal tail meet fusion sealRow transport route provenance
      name scheduleRead tailRead meetRead fusionRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier precision source window dyadic cofinal tail meet fusion
        sealRow transport route provenance name bundle pkg →
      Cont precision source scheduleRead →
        Cont scheduleRead window tailRead →
          Cont tailRead meet meetRead →
            Cont meetRead fusion fusionRead →
              Cont fusionRead sealRow sealedRead →
                PkgSig bundle sealedRead pkg →
                  SemanticNameCert
                    (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row precision ∨ hsame row source ∨ hsame row window ∨
                        hsame row dyadic ∨ hsame row cofinal ∨ hsame row tail ∨
                          hsame row meet ∨ hsame row fusion ∨ hsame row sealRow ∨
                            hsame row sealedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont precision source scheduleRead ∧
                        Cont scheduleRead window tailRead ∧ Cont tailRead meet meetRead ∧
                          Cont meetRead fusion fusionRead ∧
                            Cont fusionRead sealRow sealedRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle sealedRead pkg)
                    hsame ∧ UnaryHistory scheduleRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory meetRead ∧ UnaryHistory fusionRead ∧
                        UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier scheduleRoute tailRoute meetRoute fusionRoute sealRoute sealedPkg
  obtain ⟨precisionUnary, sourceUnary, windowUnary, _dyadicUnary, _cofinalUnary,
    _tailUnary, meetUnary, fusionUnary, sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _precisionSourceRoute, _routeWindowTail,
    _tailMeetFusion, _fusionSealTransport, provenancePkg, _namePkg⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed precisionUnary sourceUnary scheduleRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed scheduleUnary windowUnary tailRoute
  have meetReadUnary : UnaryHistory meetRead :=
    unary_cont_closed tailReadUnary meetUnary meetRoute
  have fusionReadUnary : UnaryHistory fusionRead :=
    unary_cont_closed meetReadUnary fusionUnary fusionRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed fusionReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row precision ∨ hsame row source ∨ hsame row window ∨
              hsame row dyadic ∨ hsame row cofinal ∨ hsame row tail ∨
                hsame row meet ∨ hsame row fusion ∨ hsame row sealRow ∨
                  hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont precision source scheduleRead ∧
              Cont scheduleRead window tailRead ∧ Cont tailRead meet meetRead ∧
                Cont meetRead fusion fusionRead ∧ Cont fusionRead sealRow sealedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, tailRoute, meetRoute, fusionRoute, sealRoute,
          provenancePkg, sealedPkg⟩
  }
  exact
    ⟨cert, scheduleUnary, tailReadUnary, meetReadUnary, fusionReadUnary, sealedUnary⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
