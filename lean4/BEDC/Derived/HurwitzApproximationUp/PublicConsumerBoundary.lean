import BEDC.Derived.HurwitzApproximationUp.NameCertObligations

namespace BEDC.Derived.HurwitzApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HurwitzApproximation_public_consumer_boundary [AskSetup] [PackageSetup]
    {X Q A C F S D R E T U P N inputRead prefixRead convergentRead neighborRead
      budgetRead outputRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory X ∧ UnaryHistory Q ∧ UnaryHistory A ∧ UnaryHistory C ∧
      UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧
        UnaryHistory E) →
      Cont X Q inputRead →
        Cont inputRead A prefixRead →
          Cont prefixRead C convergentRead →
            Cont convergentRead F neighborRead →
              Cont neighborRead D budgetRead →
                Cont budgetRead R outputRead →
                  Cont outputRead E sealRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        PkgSig bundle sealRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row X ∨ hsame row Q ∨ hsame row A ∨
                                  hsame row C ∨ hsame row F ∨ hsame row S ∨
                                    hsame row D ∨ hsame row R ∨ hsame row E ∨
                                      hsame row outputRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory outputRead ∧ UnaryHistory sealRead ∧
                              Cont outputRead E sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rows inputRoute prefixRoute convergentRoute neighborRoute budgetRoute outputRoute
    sealRoute provenancePkg namePkg sealPkg
  obtain ⟨cert, outputUnary⟩ :=
    HurwitzApproximationCarrier_namecert_obligations
      (X := X) (Q := Q) (A := A) (C := C) (F := F) (S := S) (D := D) (R := R)
      (E := E) (T := T) (U := U) (P := P) (N := N) (inputRead := inputRead)
      (prefixRead := prefixRead) (convergentRead := convergentRead)
      (neighborRead := neighborRead) (budgetRead := budgetRead) (outputRead := outputRead)
      (bundle := bundle) (pkg := pkg)
      rows inputRoute prefixRoute convergentRoute neighborRoute budgetRoute outputRoute
      provenancePkg namePkg
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed outputUnary rows.right.right.right.right.right.right.right.right sealRoute
  exact ⟨cert, outputUnary, sealUnary, sealRoute, sealPkg⟩

end BEDC.Derived.HurwitzApproximationUp
