#!/usr/bin/env bash
# call in top-level dir...
docker build -t protocolplatformbench/protocolplatformbench:latest -f etc/docker/Dockerfile-benchmarks .
