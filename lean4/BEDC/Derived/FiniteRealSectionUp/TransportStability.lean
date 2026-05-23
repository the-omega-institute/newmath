import BEDC.Derived.FiniteRealSectionUp.RouteConsumerExactness

namespace BEDC.Derived.FiniteRealSectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem FiniteRealSection_transport_stability [AskSetup] [PackageSetup]
    {q W R D E H C P N q' W' R' D' E' H' C' P' N' qW qWR qWRD qWRDE
      terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame q q' → hsame W W' → hsame R R' → hsame D D' → hsame E E' →
      hsame H H' → hsame C C' → hsame P P' → hsame N N' →
        UnaryHistory q → UnaryHistory W → UnaryHistory R → UnaryHistory D →
          UnaryHistory E → UnaryHistory N → Cont q W qW → Cont qW R qWR →
            Cont qWR D qWRD → Cont qWRD E qWRDE → Cont qWRDE N terminal →
              PkgSig bundle terminal pkg →
                FieldFaithful.fields (FiniteRealSectionUp.mk q' W' R' D' E' H' C' P' N') =
                    [q', W', R', D', E', H', C', P', N'] ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row qW ∨ hsame row qWR ∨ hsame row qWRD ∨
                        hsame row qWRDE ∨ hsame row terminal)
                    (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro sameQ sameW sameR sameD sameE sameH sameC sameP sameN unaryQ unaryW unaryR
    unaryD unaryE unaryN requestWindow windowReadback readbackTolerance toleranceSeal
    sealTerminal terminalPkg
  cases sameQ
  cases sameW
  cases sameR
  cases sameD
  cases sameE
  cases sameH
  cases sameC
  cases sameP
  cases sameN
  have route :=
    FiniteRealSection_route_consumer_exactness
      (q := q) (W := W) (R := R) (D := D) (E := E) (H := H) (C := C) (P := P)
      (N := N) (qW := qW) (qWR := qWR) (qWRD := qWRD) (qWRDE := qWRDE)
      (terminal := terminal) (bundle := bundle) (pkg := pkg)
      unaryQ unaryW unaryR unaryD unaryE unaryN requestWindow windowReadback
      readbackTolerance toleranceSeal sealTerminal terminalPkg
  exact ⟨route.left, route.right.right⟩

end BEDC.Derived.FiniteRealSectionUp
