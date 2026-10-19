import BMLean.Tables
import BMLean.Data.Hub038

namespace BMC

theorem hubOk_038 : hubChunkOk (parseRows BMD.hub038) = true := by native_decide

end BMC
