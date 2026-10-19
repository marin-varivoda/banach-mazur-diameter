import BMLean.Tables
import BMLean.Data.Hub010

namespace BMC

theorem hubOk_010 : hubChunkOk (parseRows BMD.hub010) = true := by native_decide

end BMC
