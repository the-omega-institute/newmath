import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ValidatedNumericsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ValidatedNumericsReadbackPacket_real_readback_soundness [AskSetup] [PackageSetup]
    {interval precision modulus observation readback containment provenance name finiteRead
      sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval ->
      UnaryHistory precision ->
        UnaryHistory modulus ->
          UnaryHistory observation ->
            UnaryHistory readback ->
              UnaryHistory containment ->
                UnaryHistory provenance ->
                  UnaryHistory name ->
                    Cont modulus precision observation ->
                      Cont observation readback finiteRead ->
                        Cont interval containment sealRow ->
                          PkgSig bundle name pkg ->
                            PkgSig bundle sealRow pkg ->
                              UnaryHistory finiteRead ∧
                                UnaryHistory sealRow ∧
                                  Cont modulus precision observation ∧
                                    Cont observation readback finiteRead ∧
                                      Cont interval containment sealRow ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle sealRow pkg := by
  intro intervalUnary _precisionUnary _modulusUnary observationUnary readbackUnary containmentUnary
  intro _provenanceUnary _nameUnary modulusPrecision observationReadback intervalContainment
  intro namePkg sealPkg
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed observationUnary readbackUnary observationReadback
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed intervalUnary containmentUnary intervalContainment
  exact ⟨finiteReadUnary, sealRowUnary, modulusPrecision, observationReadback, intervalContainment,
    namePkg, sealPkg⟩

end BEDC.Derived.ValidatedNumericsUp
