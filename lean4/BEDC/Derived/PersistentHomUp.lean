import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PersistentHomUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PersistentHomFiltrationCarrier [AskSetup] [PackageSetup]
    (simplicialSource homologyRows indexSpine boundaryRoutes persistenceRoutes barcodeRows
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory simplicialSource ∧ UnaryHistory homologyRows ∧ UnaryHistory indexSpine ∧
    UnaryHistory boundaryRoutes ∧ UnaryHistory persistenceRoutes ∧ UnaryHistory barcodeRows ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        Cont simplicialSource homologyRows boundaryRoutes ∧
          Cont boundaryRoutes persistenceRoutes barcodeRows ∧
            Cont provenance barcodeRows endpoint ∧ PkgSig bundle endpoint pkg

theorem PersistentHomFiltrationCarrier_source_boundary [AskSetup] [PackageSetup]
    {simplicialSource homologyRows indexSpine boundaryRoutes persistenceRoutes barcodeRows
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PersistentHomFiltrationCarrier simplicialSource homologyRows indexSpine boundaryRoutes
        persistenceRoutes barcodeRows provenance endpoint bundle pkg ->
      UnaryHistory simplicialSource ∧ UnaryHistory homologyRows ∧ UnaryHistory indexSpine ∧
        Cont simplicialSource homologyRows boundaryRoutes ∧
          Cont boundaryRoutes persistenceRoutes barcodeRows ∧
            Cont provenance barcodeRows endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.PersistentHomUp
