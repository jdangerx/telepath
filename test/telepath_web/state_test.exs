defmodule Telepath.StateTest do
  use ExUnit.Case, async: true

  test "stores user message" do
    {:ok, _bucket} = Telepath.State.start_link()
    assert Telepath.State.get_all() == %{}

    Telepath.State.put("eyy", "i'm walking here")
    assert Telepath.State.get_all() == %{"eyy" => "i'm walking here"}
  end
end
