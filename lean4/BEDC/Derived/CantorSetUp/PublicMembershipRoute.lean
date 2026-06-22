import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetPublicMembershipRoute [AskSetup] [PackageSetup]
    {T G I D R E H K P N prefixRead intervalRead endpointRead regularRead sealedRead
      publicRead boundedRead finiteNetRead closedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead →
      Cont prefixRead I intervalRead →
        Cont intervalRead D endpointRead →
          Cont endpointRead R regularRead →
            Cont regularRead E sealedRead →
              Cont sealedRead N publicRead →
                Cont publicRead H boundedRead →
                  Cont publicRead K finiteNetRead →
                    Cont publicRead P closedRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          UnaryHistory T →
                            UnaryHistory G →
                              UnaryHistory I →
                                UnaryHistory D →
                                  UnaryHistory R →
                                    UnaryHistory E →
                                      UnaryHistory H →
                                        UnaryHistory K →
                                          UnaryHistory P →
                                            UnaryHistory N →
                                              SemanticNameCert
                                                  (fun row : BHist =>
                                                    hsame row publicRead ∧ UnaryHistory row)
                                                  (fun row : BHist =>
                                                    hsame row T ∨ hsame row G ∨
                                                      hsame row I ∨ hsame row D ∨
                                                        hsame row R ∨ hsame row E ∨
                                                          hsame row boundedRead ∨
                                                            hsame row finiteNetRead ∨
                                                              hsame row closedRead ∨
                                                                hsame row publicRead)
                                                  (fun row : BHist =>
                                                    UnaryHistory row ∧
                                                      Cont endpointRead R regularRead ∧
                                                        Cont regularRead E sealedRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                                  hsame ∧
                                                UnaryHistory boundedRead ∧
                                                  UnaryHistory finiteNetRead ∧
                                                    UnaryHistory closedRead ∧
                                                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixRoute intervalRoute endpointRoute regularRoute sealedRoute publicRoute
    boundedRoute finiteNetRoute closedRoute pkgP pkgN unaryT unaryG unaryI unaryD unaryR
    unaryE unaryH unaryK unaryP unaryN
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryT unaryG prefixRoute
  have intervalUnary : UnaryHistory intervalRead :=
    unary_cont_closed prefixUnary unaryI intervalRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed intervalUnary unaryD endpointRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointUnary unaryR regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary unaryE sealedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealedUnary unaryN publicRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed publicUnary unaryH boundedRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed publicUnary unaryK finiteNetRoute
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed publicUnary unaryP closedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row boundedRead ∨ hsame row finiteNetRead ∨
                hsame row closedRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpointRead R regularRead ∧
              Cont regularRead E sealedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regularRoute, sealedRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, boundedUnary, finiteNetUnary, closedUnary, publicUnary⟩

end BEDC.Derived.CantorSetUp
