import BMLean.Tables
import BMLean.Data.Hub004

namespace BMC

theorem hubOk_004 : hubChunkOk (parseRows BMD.hub004) = true := by native_decide

end BMC
