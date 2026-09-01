import Spikes.«3_Gzip».Plan

namespace Grass.Spikes.Gzip

def lengthBase : Vec UInt16 29 :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43,
    51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

def lengthExtra : Vec UInt8 29 :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3,
    4, 4, 4, 4, 5, 5, 5, 5, 0]

def distanceBase : Vec UInt16 30 :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257,
    385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385,
    24577]

def distanceExtra : Vec UInt8 30 :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8,
    9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

def gzipStaticObjects : StaticObjectTable := static_objects {
  rodata align 2 {
    lengthBase: uint16s lengthBase
    lengthExtra: uint8s lengthExtra
    distanceBase: uint16s distanceBase
    distanceExtra: uint8s distanceExtra
  }
}

def gzipImports : ImportTable := imports {
  KERNEL32.dll {
    GetStdHandle
    GetProcessHeap
    HeapAlloc
    ReadFile
    WriteFile
    ExitProcess
  }
}

end Grass.Spikes.Gzip
