import BEDC.Derived.RealModulusPurityBoundaryUp.ScopePackage

namespace BEDC.Derived.RealModulusPurityBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealModulusPurityBoundaryScopeBinding [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB predicted consumer scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] ->
      Cont D S R0 ->
        Cont R0 L routeRL ->
          Cont routeRL B routeLB ->
            Cont routeLB H predicted ->
              Cont routeLB N consumer ->
                Cont predicted consumer scopedRead ->
                  UnaryHistory D ->
                    UnaryHistory S ->
                      UnaryHistory L ->
                        UnaryHistory B ->
                          UnaryHistory H ->
                            UnaryHistory N ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  PkgSig bundle scopedRead pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row scopedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row D ∨ hsame row S ∨ hsame row R0 ∨
                                            hsame row L ∨ hsame row B ∨ hsame row H ∨
                                              hsame row N ∨ hsame row predicted ∨
                                                hsame row consumer ∨ hsame row scopedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont D S R0 ∧
                                            Cont R0 L routeRL ∧ Cont routeRL B routeLB ∧
                                              Cont routeLB H predicted ∧
                                                Cont routeLB N consumer ∧
                                                  Cont predicted consumer scopedRead ∧
                                                    PkgSig bundle P pkg)
                                        hsame ∧
                                      UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields routeR0 routeRLCont routeLBCont predictedCont consumerCont scopedCont
    unaryD unaryS unaryL unaryB unaryH unaryN provenancePkg namePkg scopedPkg
  have _fieldsWitness :
      realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] :=
    fields
  have _namePkgWitness : PkgSig bundle N pkg := namePkg
  have _scopedPkgWitness : PkgSig bundle scopedRead pkg := scopedPkg
  have routeR0Unary : UnaryHistory R0 :=
    unary_cont_closed unaryD unaryS routeR0
  have routeRLUnary : UnaryHistory routeRL :=
    unary_cont_closed routeR0Unary unaryL routeRLCont
  have routeLBUnary : UnaryHistory routeLB :=
    unary_cont_closed routeRLUnary unaryB routeLBCont
  have predictedUnary : UnaryHistory predicted :=
    unary_cont_closed routeLBUnary unaryH predictedCont
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeLBUnary unaryN consumerCont
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed predictedUnary consumerUnary scopedCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row N ∨ hsame row predicted ∨ hsame row consumer ∨
                hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB H predicted ∧
                Cont routeLB N consumer ∧ Cont predicted consumer scopedRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead
        ⟨hsame_refl scopedRead, scopedUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeR0, routeRLCont, routeLBCont, predictedCont, consumerCont,
          scopedCont, provenancePkg⟩
  }
  exact ⟨cert, scopedUnary⟩

end BEDC.Derived.RealModulusPurityBoundaryUp
