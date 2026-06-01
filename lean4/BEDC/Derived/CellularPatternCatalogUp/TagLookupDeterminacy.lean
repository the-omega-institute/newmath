import BEDC.Derived.CellularPatternCatalogUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.CellularPatternCatalogUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CellularPatternCatalog_tag_lookup_determinacy [AskSetup] [PackageSetup]
    {R W T G H C P N R' W' T' G' H' C' P' N' lookup lookup' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont R W lookup ->
      Cont R' W' lookup' ->
        Cont lookup G T ->
          Cont lookup' G' T' ->
            hsame R R' ->
              hsame W W' ->
                hsame G G' ->
                  hsame H H' ->
                    hsame C C' ->
                      hsame P P' ->
                        hsame N N' ->
                          PkgSig bundle N pkg ->
                            hsame lookup lookup' ∧ hsame T T' ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro leftLookup rightLookup leftTag rightTag sameRule sameWindow sameCatalog _sameTransport
    _sameRoute _sameProvenance _sameName pkgN
  have sameLookup : hsame lookup lookup' :=
    cont_respects_hsame sameRule sameWindow leftLookup rightLookup
  have sameTag : hsame T T' :=
    cont_respects_hsame sameLookup sameCatalog leftTag rightTag
  exact ⟨sameLookup, sameTag, pkgN⟩

end BEDC.Derived.CellularPatternCatalogUp
