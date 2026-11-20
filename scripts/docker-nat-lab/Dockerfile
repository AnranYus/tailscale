FROM golang:1.26-alpine

RUN apk add --no-cache iptables iproute2 tcpdump bash

COPY bin/tailscaled /usr/local/bin/tailscaled
COPY bin/tailscale /usr/local/bin/tailscale
COPY bin/testcontrol /usr/local/bin/testcontrol
COPY bin/stund /usr/local/bin/stund
RUN chmod +x /usr/local/bin/tailscaled /usr/local/bin/tailscale /usr/local/bin/testcontrol /usr/local/bin/stund
