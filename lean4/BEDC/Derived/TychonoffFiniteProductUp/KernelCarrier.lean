import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TychonoffFiniteProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TychonoffFiniteProductCarrier [AskSetup] [PackageSetup]
    (I X K T L M H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory I ∧ UnaryHistory X ∧ UnaryHistory K ∧ UnaryHistory T ∧
    UnaryHistory L ∧ UnaryHistory M ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont I X K ∧ Cont K T L ∧ Cont L M H ∧
        Cont H C N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame N M

theorem TychonoffFiniteProductNameCertObligations [AskSetup] [PackageSetup]
    {I X K T L M H C P N netRead limitRead productRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TychonoffFiniteProductCarrier I X K T L M H C P N bundle pkg →
      Cont K T netRead →
        Cont L M limitRead →
          Cont netRead limitRead productRead →
            PkgSig bundle productRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row N ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row K ∨ hsame row T ∨ hsame row L ∨
                      hsame row M ∨ hsame row productRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont netRead limitRead productRead ∧
                      PkgSig bundle productRead pkg)
                  hsame ∧
                UnaryHistory netRead ∧ UnaryHistory limitRead ∧
                  UnaryHistory productRead := by
  -- BEDC touchpoint anchor: TychonoffFiniteProductCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier netRoute limitRoute productRoute productPkg
  obtain ⟨_indexUnary, _coordinateUnary, compactUnary, netUnary, limitUnary,
    metricUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    _indexCoordinateCompact, _compactNetLimit, _limitMetricTransport,
    _transportRouteName, _provenancePkg, _namePkg, nameMetric⟩ := carrier
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed compactUnary netUnary netRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed limitUnary metricUnary limitRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed netReadUnary limitReadUnary productRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row K ∨ hsame row T ∨ hsame row L ∨
              hsame row M ∨ hsame row productRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont netRead limitRead productRead ∧
              PkgSig bundle productRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nameUnary⟩
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
      exact Or.inl (hsame_trans source.left nameMetric)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, productRoute, productPkg⟩
  }
  exact ⟨cert, netReadUnary, limitReadUnary, productReadUnary⟩

end BEDC.Derived.TychonoffFiniteProductUp
