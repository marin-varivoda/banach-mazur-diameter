import BMLean.Tables
import BMLean.Data.Hub046

namespace BMC

theorem hubOk_046 : hubChunkOk (parseRows BMD.hub046) = true := by native_decide

end BMC
