defmodule Telepath.State do
  use Agent

  def start_link(_opts \\ []) do
    Agent.start_link(fn -> %{} end, name: __MODULE__)
  end

  def put(user, msg) do
    Agent.update(__MODULE__, &Map.put(&1, user, msg))
  end

  def delete(user) do
    Agent.update(__MODULE__, &Map.delete(&1, user))
  end

  def get(user) do
    Agent.get(__MODULE__, &Map.get(&1, user))
  end

  def get_all() do
    Agent.get(__MODULE__, fn messages -> messages end)
  end

end
