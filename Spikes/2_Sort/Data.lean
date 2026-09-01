import Spikes.«2_Sort».Plan

namespace Grass.Spikes.Sort

def sortStaticObjects : StaticObjectTable := static_objects {
  rodata align 1 {
    lf_byte: bytes #[10]
  }
  bss align 64 {
    output_buffer: zero 65536
  }
}

def sortImports : ImportTable := imports {
  KERNEL32.dll {
    GetStdHandle
    GetProcessHeap
    HeapAlloc
    HeapReAlloc
    ReadFile
    WriteFile
    ExitProcess
  }
}

end Grass.Spikes.Sort
