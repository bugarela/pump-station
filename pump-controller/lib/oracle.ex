defmodule Oracle do
  @water_level_changes ["waterLevelUp", "waterLevelDown"]
  @pump_status_changes ["successON", "successOFF"]

  def start do
    :global.register_name("oracle", self())

    listen()
  end

  def listen do
    IO.puts "Oracle at [#{inspect self()}] is listening"

    receive do
      {p, as} when not is_atom(p) -> options = input_option(as); IO.inspect(options); send p, {:ok, options}
    end

    listen()
  end

  def input_option(actions) do
    IO.inspect(actions)
    enumerated_actions = actions |> Enum.with_index |> Enum.map(fn({x, i}) -> "#{i} => #{x}" end)
    IO.puts (inspect enumerated_actions)

    [action, parameters] =  Enum.at(actions, 0)|> String.split("(")
    parameter = parameters |> String.trim_trailing(")")

    cond do
      Enum.member?(@water_level_changes, action) ->
        IO.puts("Waiting level change")
        read_water_level
      Enum.member?(@pump_status_changes, action) ->
        IO.puts("Waiting pump status for pump " <> parameter)
        read_pump_status(parameter)
      true -> 0
    end
  end

  def read_water_level do
    receive do
      {:water_level_change, direction} -> IO.inspect(direction); if direction == "up", do: 0, else: 1
    end
  end

  def read_pump_status(pump) do
    receive do
      {:pump_status_change, p, status} when pump == p -> IO.inspect(status); if status == "healthy", do: 0, else: 1
    end
  end
end
