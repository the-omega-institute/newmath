import BEDC.Derived.RegularCauchyAbsUp.ObligationClosure
import BEDC.Derived.RegularCauchyAbsUp.PublicExportSurface
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyAbsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAbsCarrier_bridge_boundary_reader [AskSetup] [PackageSetup]
    {X W D V R E H C P N windowRead endpointRead absRead realRead publicRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X -> UnaryHistory W -> UnaryHistory D -> UnaryHistory V -> UnaryHistory R ->
      UnaryHistory E -> UnaryHistory N -> UnaryHistory publicRead ->
        Cont X W windowRead -> Cont windowRead D endpointRead -> Cont endpointRead V absRead ->
          Cont absRead R realRead -> Cont R E realRead -> Cont realRead N publicRead ->
            Cont publicRead N bridgeRead -> PkgSig bundle R pkg ->
              PkgSig bundle publicRead pkg -> PkgSig bundle bridgeRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    (hsame row publicRead ∨ hsame row realRead ∨ hsame row R) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row realRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont X W windowRead ∧
                      Cont windowRead D endpointRead ∧ Cont endpointRead V absRead ∧
                        Cont absRead R realRead ∧ Cont R E realRead ∧
                          Cont realRead N publicRead ∧ PkgSig bundle R pkg ∧
                            PkgSig bundle publicRead pkg)
                  hsame ∧ UnaryHistory bridgeRead ∧ Cont publicRead N bridgeRead ∧
                    PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryX unaryW unaryD unaryV unaryR unaryE unaryN unaryPublic xWindow
    windowEndpoint endpointAbs absReal realSeal realPublic publicBridge rPkg publicPkg
    bridgePkg
  have publicSurface :=
    RegularCauchyAbsCarrier_public_export_surface
      (X := X) (W := W) (D := D) (V := V) (R := R) (E := E) (H := H) (C := C)
      (P := P) (N := N) (windowRead := windowRead) (endpointRead := endpointRead)
      (absRead := absRead) (realRead := realRead) (publicRead := publicRead)
      (bundle := bundle) (pkg := pkg) unaryX unaryW unaryD unaryV unaryR unaryE
      unaryPublic xWindow windowEndpoint endpointAbs absReal realSeal realPublic rPkg publicPkg
  have publicCert :
      SemanticNameCert
        (fun row : BHist =>
          (hsame row publicRead ∨ hsame row realRead ∨ hsame row R) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row realRead ∨ hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont X W windowRead ∧ Cont windowRead D endpointRead ∧
            Cont endpointRead V absRead ∧ Cont absRead R realRead ∧ Cont R E realRead ∧
              Cont realRead N publicRead ∧ PkgSig bundle R pkg ∧
                PkgSig bundle publicRead pkg)
        hsame :=
    publicSurface.left
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed unaryPublic unaryN publicBridge
  exact ⟨publicCert, bridgeUnary, publicBridge, bridgePkg⟩

theorem RegularCauchyAbsCarrier_mature_treatment [AskSetup] [PackageSetup]
    {X W D V R E H C P N windowRead endpointRead absRead realRead publicRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X -> UnaryHistory W -> UnaryHistory D -> UnaryHistory V -> UnaryHistory R ->
      UnaryHistory E -> UnaryHistory N -> UnaryHistory publicRead ->
        Cont X W windowRead -> Cont windowRead D endpointRead -> Cont endpointRead V absRead ->
          Cont absRead R realRead -> Cont R E realRead -> Cont realRead N publicRead ->
            Cont publicRead N bridgeRead -> PkgSig bundle R pkg ->
              PkgSig bundle publicRead pkg -> PkgSig bundle bridgeRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
                  hsame ∧
                SemanticNameCert
                  (fun row : BHist =>
                    (hsame row publicRead ∨ hsame row realRead ∨ hsame row R) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row realRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont X W windowRead ∧
                      Cont windowRead D endpointRead ∧ Cont endpointRead V absRead ∧
                        Cont absRead R realRead ∧ Cont R E realRead ∧
                          Cont realRead N publicRead ∧ PkgSig bundle R pkg ∧
                            PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory bridgeRead ∧ Cont publicRead N bridgeRead ∧
                  PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryX unaryW unaryD unaryV unaryR unaryE unaryN unaryPublic xWindow
    windowEndpoint endpointAbs absReal realSeal realPublic publicBridge rPkg publicPkg
    bridgePkg
  have obligationCert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        hsame :=
    RegularCauchyAbsCarrier_namecert_obligations X W D V R E H C P N
  have bridgeSurface :=
    RegularCauchyAbsCarrier_bridge_boundary_reader
      (X := X) (W := W) (D := D) (V := V) (R := R) (E := E) (H := H) (C := C)
      (P := P) (N := N) (windowRead := windowRead) (endpointRead := endpointRead)
      (absRead := absRead) (realRead := realRead) (publicRead := publicRead)
      (bridgeRead := bridgeRead) (bundle := bundle) (pkg := pkg) unaryX unaryW unaryD
      unaryV unaryR unaryE unaryN unaryPublic xWindow windowEndpoint endpointAbs absReal
      realSeal realPublic publicBridge rPkg publicPkg bridgePkg
  exact ⟨obligationCert, bridgeSurface⟩

end BEDC.Derived.RegularCauchyAbsUp
