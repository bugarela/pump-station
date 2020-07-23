defmodule SensorsHandler do
  use Tortoise.Handler
  require Logger

  def init(args) do
    pumps = WaterPump.pumps() |> Enum.map(fn p -> {p, ""} end) |> Enum.into(%{})
    state = %{
      pumps: pumps,
      water_level: 120
    }

    {:ok, state}
  end

  def connection(status, state) do
    # `status` will be either `:up` or `:down`; you can use this to
    # inform the rest of your system if the connection is currently
    # open or closed; tortoise should be busy reconnecting if you get
    # a `:down`
    {:ok, state}
  end

  #  topic filter room/+/temp
  def handle_message(["pumps", pump, "state"], payload, state) do
    # :ok = Temperature.record(room, payload)
    {p, ""} = Integer.parse(pump)

    send :global.whereis_name("oracle"), { :pump_status_change, pump, payload }

    state = %{state | pumps: %{ state[:pumps] | p => payload }}

    {:ok, state}
  end

  def handle_message(["water_level"], payload, state) do
    # unhandled message! You will crash if you subscribe to something
    # and you don't have a 'catch all' matcher; crashing on unexpected
    # messages could be a strategy though.

    send :global.whereis_name("oracle"), { :water_level_change, payload }

    state = %{state | water_level: payload}

    {:ok, state}
  end

  def subscription(status, topic_filter, state) do
    {:ok, state}
  end

  def terminate(reason, state) do
    # tortoise doesn't care about what you return from terminate/2,
    # that is in alignment with other behaviours that implement a
    # terminate-callback
    :ok
  end
end
