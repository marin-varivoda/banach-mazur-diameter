import BMLean.Tables
import BMLean.Data.Hub043

namespace BMC

theorem hubOk_043 : hubChunkOk (parseRows BMD.hub043) = true := by native_decide

end BMC
