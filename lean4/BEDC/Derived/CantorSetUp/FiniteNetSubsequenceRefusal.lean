import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetCarrier_finite_net_subsequence_refusal [AskSetup] [PackageSetup]
    {T G I D R E H K P N prefixRead gapRead endpointRead regularRead sealedRead
      boundedRead finiteNetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead →
      Cont prefixRead I gapRead →
        Cont gapRead D endpointRead →
          Cont endpointRead R regularRead →
            Cont regularRead E sealedRead →
              Cont sealedRead H boundedRead →
                Cont boundedRead K finiteNetRead →
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
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row finiteNetRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row T ∨ hsame row G ∨ hsame row I ∨
                                              hsame row D ∨ hsame row R ∨ hsame row E ∨
                                                hsame row H ∨ hsame row K ∨
                                                  hsame row finiteNetRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont sealedRead H boundedRead ∧
                                              Cont boundedRead K finiteNetRead ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory prefixRead ∧ UnaryHistory gapRead ∧
                                          UnaryHistory endpointRead ∧ UnaryHistory regularRead ∧
                                            UnaryHistory sealedRead ∧ UnaryHistory boundedRead ∧
                                              UnaryHistory finiteNetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro prefixRoute gapRoute endpointRoute regularRoute sealedRoute boundedRoute finiteNetRoute
    pkgP pkgN unaryT unaryG unaryI unaryD unaryR unaryE unaryH unaryK
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryT unaryG prefixRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed prefixUnary unaryI gapRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed gapUnary unaryD endpointRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointUnary unaryR regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary unaryE sealedRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed sealedUnary unaryH boundedRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed boundedUnary unaryK finiteNetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finiteNetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row K ∨ hsame row finiteNetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sealedRead H boundedRead ∧
              Cont boundedRead K finiteNetRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro finiteNetRead ⟨hsame_refl finiteNetRead, finiteNetUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundedRoute, finiteNetRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert, prefixUnary, gapUnary, endpointUnary, regularUnary, sealedUnary, boundedUnary,
      finiteNetUnary⟩

end BEDC.Derived.CantorSetUp
