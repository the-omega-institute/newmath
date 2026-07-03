import BEDC.Derived.ParsevalUp.NameCertObligations

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalPublicEnergyExport [AskSetup] [PackageSetup]
    {F S I E R D L H C P N coefficientRead energyRead toleranceRead sealRead scopedRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrierSurface F S I E R D L H C P N bundle pkg →
      Cont F S coefficientRead →
        Cont I E energyRead →
          Cont energyRead D toleranceRead →
            Cont toleranceRead L sealRead →
              Cont sealRead C scopedRead →
                Cont scopedRead N publicRead →
                  PkgSig bundle publicRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨
                            hsame row D ∨ hsame row L ∨ hsame row C ∨ hsame row N ∨
                              hsame row publicRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont F S coefficientRead ∧
                            Cont I E energyRead ∧ Cont energyRead D toleranceRead ∧
                              Cont toleranceRead L sealRead ∧ Cont sealRead C scopedRead ∧
                                Cont scopedRead N publicRead ∧ PkgSig bundle publicRead pkg)
                        hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: ParsevalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute energyRoute toleranceRoute sealRoute scopedRoute publicRoute
    publicPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, scopedEndpointUnary, _provenanceUnary,
    localNameUnary,
    _scopedPkg, _localNamePkg⟩ := carrier
  have _coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary energyRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed energyUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed sealReadUnary scopedEndpointUnary scopedRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed scopedReadUnary localNameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨ hsame row D ∨
              hsame row L ∨ hsame row C ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F S coefficientRead ∧ Cont I E energyRead ∧
              Cont energyRead D toleranceRead ∧ Cont toleranceRead L sealRead ∧
                Cont sealRead C scopedRead ∧ Cont scopedRead N publicRead ∧
                  PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coefficientRoute, energyRoute, toleranceRoute, sealRoute, scopedRoute,
          publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicReadUnary⟩

end BEDC.Derived.ParsevalUp
