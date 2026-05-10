import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TannakaKreinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TannakaKreinFiberFunctorCarrier [AskSetup] [PackageSetup]
    (lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lieGroup ∧ UnaryHistory monoidalCat ∧ UnaryHistory fiberFunctor ∧
    UnaryHistory representation ∧ UnaryHistory unitRow ∧
      Cont lieGroup monoidalCat reconstructionLedger ∧
        Cont fiberFunctor representation tensorProduct ∧ Cont unitRow tensorProduct provenance ∧
          Cont provenance reconstructionLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem TannakaKreinFiberFunctorCarrier_source_boundary [AskSetup] [PackageSetup]
    {lieGroup monoidalCat fiberFunctor representation unitRow tensorProduct
      reconstructionLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TannakaKreinFiberFunctorCarrier lieGroup monoidalCat fiberFunctor representation unitRow
        tensorProduct reconstructionLedger provenance endpoint bundle pkg ->
      UnaryHistory lieGroup ∧ UnaryHistory monoidalCat ∧ UnaryHistory fiberFunctor ∧
        UnaryHistory representation ∧ UnaryHistory unitRow ∧ UnaryHistory tensorProduct ∧
          UnaryHistory reconstructionLedger ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
            hsame reconstructionLedger (append lieGroup monoidalCat) ∧
              hsame tensorProduct (append fiberFunctor representation) ∧
                hsame provenance (append unitRow tensorProduct) ∧
                  hsame endpoint (append provenance reconstructionLedger) ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier
  have lieGroupUnary : UnaryHistory lieGroup := carrier.left
  have monoidalCatUnary : UnaryHistory monoidalCat := carrier.right.left
  have fiberFunctorUnary : UnaryHistory fiberFunctor := carrier.right.right.left
  have representationUnary : UnaryHistory representation := carrier.right.right.right.left
  have unitRowUnary : UnaryHistory unitRow := carrier.right.right.right.right.left
  have reconstructionLedgerCont : Cont lieGroup monoidalCat reconstructionLedger :=
    carrier.right.right.right.right.right.left
  have tensorProductCont : Cont fiberFunctor representation tensorProduct :=
    carrier.right.right.right.right.right.right.left
  have provenanceCont : Cont unitRow tensorProduct provenance :=
    carrier.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance reconstructionLedger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have reconstructionLedgerUnary : UnaryHistory reconstructionLedger :=
    unary_cont_closed lieGroupUnary monoidalCatUnary reconstructionLedgerCont
  have tensorProductUnary : UnaryHistory tensorProduct :=
    unary_cont_closed fiberFunctorUnary representationUnary tensorProductCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed unitRowUnary tensorProductUnary provenanceCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary reconstructionLedgerUnary endpointCont
  exact And.intro lieGroupUnary
    (And.intro monoidalCatUnary
      (And.intro fiberFunctorUnary
        (And.intro representationUnary
          (And.intro unitRowUnary
            (And.intro tensorProductUnary
              (And.intro reconstructionLedgerUnary
                (And.intro provenanceUnary
                  (And.intro endpointUnary
                    (And.intro reconstructionLedgerCont
                      (And.intro tensorProductCont
                        (And.intro provenanceCont
                          (And.intro endpointCont pkgSig))))))))))))

end BEDC.Derived.TannakaKreinUp
