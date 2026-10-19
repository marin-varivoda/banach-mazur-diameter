import BMLean.Tables
import BMLean.Data.Hub027

namespace BMC

theorem hubOk_027 : hubChunkOk (parseRows BMD.hub027) = true := by native_decide

end BMC
