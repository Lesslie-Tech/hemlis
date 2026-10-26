defmodule Foo do
  def go, do: Util.psm(Unused.A).usedByScan()
end
