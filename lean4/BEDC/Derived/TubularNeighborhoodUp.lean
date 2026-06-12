import BEDC.FKernel.Hist

namespace BEDC.Derived.TubularNeighborhoodUp

open BEDC.FKernel.Hist

inductive TubularNeighborhoodUp : Type where
  | mk
      (source normal metric chart radius image transport replay provenance localName : BHist) :
      TubularNeighborhoodUp

def carrierRows : TubularNeighborhoodUp → List BHist
  | TubularNeighborhoodUp.mk source normal metric chart radius image transport replay provenance localName =>
      [source, normal, metric, chart, radius, image, transport, replay, provenance, localName]

end BEDC.Derived.TubularNeighborhoodUp
