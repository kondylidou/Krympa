import math
import sys
import logging
import time
from typing import Tuple, List, TypeAlias

import config
import config_schedules
from run.utils import PROVER_PROCESSES
from run.heuristic import get_heuristic, Heuristic
from run.problem import _Problem
from run.process import (
    is_time_left,
    get_time_left,
    start_prover_process,
    check_prover_processes_terminated,
)

log = logging.getLogger()

TScheduleConf: TypeAlias = List[List[Tuple[str, int | float | None]]]
TSchedule: TypeAlias = List[Tuple[str, float]]


class Schedule:
    def __init__(
        self,
        schedule_name: str,
        schedule_conf: TSchedule,
        no_cores: int,
        context: str,
        **kwargs,
    ):
        self.__name = schedule_name
        self.__conf = schedule_conf
        assert no_cores >= 1, "Schedule need at least one core"
        self.__no_cores = no_cores

        self.index = 0

        # Load the configuration as heuristics
        self._load_schedule_heuristics(context, **kwargs)

    @property
    def name(self):
        return self.__name

    @property
    def conf(self):
        return self.__conf

    @property
    def no_cores(self):
        return self.__no_cores

    def _load_schedule_heuristics(self, context: str, **kwargs):
        self.heuristics = [
            get_heuristic(heur_path, heuristic_context=context, **kwargs)
            for (heur_path, _) in self.conf
        ]

    def get_next_heuristic(self, time_left: float) -> Tuple[Heuristic, float]:
        running_time = _compute_heuristic_timeout(
            self.index,
            len(self.conf),
            self.no_cores,
            self.conf[self.index][1],
            time_left,
        )
        heuristic = self.heuristics[self.index]
        self.index += 1
        return heuristic, running_time

    def reset(self) -> None:
        # Reset the index counter
        self.index = 0

    def heuristics_left(self) -> bool:
        return self.index < len(self.conf)

    def __len__(self):
        return len(self.conf)

    def __str__(self) -> str:
        return f"{self.name}:{self.conf}"


def _compute_heuristic_timeout(
    current_index: int,
    max_index: int,
    no_cores: int,
    assigned_time: int,
    time_left: float,
) -> float:
    # If last call on a core, run until timeout
    if max_index - current_index <= no_cores:
        return time_left

    # Run the minimum of the time-left or the assigned time
    return float(min(time_left, assigned_time))


def get_schedule_from_dict(schedule_name: str) -> TScheduleConf:
    try:
        schedule_conf = config_schedules.SCHEDULES[schedule_name]
        log.info(f"Obtained schedule: {schedule_name}")
    except KeyError:
        log.error(f'The schedule "{schedule_name}" is not implemented.')
        sys.exit(1)

    return schedule_conf


def get_schedule(schedule_name: str, context: str, no_cores: int, **kwargs) -> Schedule:
    # Load schedule from dict
    schedule_conf = get_schedule_from_dict(schedule_name)

    # Flatten the schedule
    schedule_conf_flattened = flatten_schedule(schedule_conf)

    # Initialise the schedule
    schedule = Schedule(
        schedule_name, schedule_conf_flattened, no_cores, context, **kwargs
    )
    log.info(f"Final schedule: {schedule}")
    return schedule


def flatten_schedule(
    schedule_conf: TScheduleConf,
) -> TSchedule:
    # Hold the start time of each heuristic
    start_times = {}
    # Hold the assigned runtime of each heuristic
    run_times = {}

    for core in schedule_conf:
        # The start time on a core is always zero
        time_slice = 0.0
        for heur, run_time in core:
            # Set unbounded to infinite
            if run_time is None:
                run_time = math.inf
            else:
                run_time = float(run_time)

            # Extract the runtime
            run_times[heur] = run_time
            # Set the start time of the heuristic
            start_times[heur] = time_slice
            # Increment the time
            time_slice += run_time

    # Sort heuristics according to their start times
    heur_order = [k for k, _ in sorted(start_times.items(), key=lambda item: item[1])]

    # Rebuild flat schedule
    flattened = []
    for heur in heur_order:
        flattened += [(heur, run_times[heur])]

    return flattened


def to_start_new_process(
    schedule: Schedule, problem: _Problem, start_time: float, time_limit: float
) -> bool:
    # If there are more heuristics left, timeout is not met and the problem is not solved
    # - keep starting new prover processes
    return (
        schedule.heuristics_left()
        and is_time_left(start_time, time_limit)
        and not problem.solved
    )


def wait_for_processes_to_terminate(
    schedule: Schedule, problem: _Problem, start_time: float, time_limit: float
) -> bool:
    # If problem is unsolved, all cores are in use, or all available schedule is running, sleep until a schedule
    # stops or the problem is solved.
    return (
        (len(PROVER_PROCESSES) >= schedule.no_cores or not schedule.heuristics_left())
        and not problem.solved
        and is_time_left(start_time, time_limit)
        and len(PROVER_PROCESSES) > 0
    )


def run_schedule(
    problem: _Problem,
    schedule: Schedule,
    time_limit: float,
) -> _Problem:
    # Set the start time
    start_time = time.time()

    while to_start_new_process(schedule, problem, start_time, time_limit):
        # Compute the time left
        log.debug(f"Time left: {time_limit - (time.time() - start_time):.2}")

        # Start the prover process
        next_heuristic, runtime = schedule.get_next_heuristic(
            get_time_left(start_time, time_limit)
        )
        start_prover_process(next_heuristic, problem, runtime)

        while wait_for_processes_to_terminate(
            schedule, problem, start_time, time_limit
        ):
            # Set program to sleep
            time.sleep(config.PROVER_PROC_SLEEP_TIME)
            log.debug(f"Time used: {time.time() - start_time:.2f}")

            # Check if some processes have terminated
            problem = check_prover_processes_terminated(problem)

    # Return the problem
    return problem
