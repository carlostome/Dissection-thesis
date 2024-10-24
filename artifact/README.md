# Artifact

This artifact uses _Agda_ version 2.5.4.2 and Agda standard library version 0.16.1

## Docker

To ease the inspection of the artifact we include a docker file to build an
image that contains the necessary tooling and emacs.

To build the image execute:

```
docker build . -t "artifact"
```
    
To run emacs via X11 inside the container:

```
docker run -it --rm --network=host --ipc=host --shm-size=4g -v /tmp/.X11-unix:/tmp/.X11-unix:ro -v "/home/carlos/.Xauthority:/root/.Xauthority" -e DISPLAY -e XAUTHORITY=/root/.Xauthority artifact:latest bash -i -c "emacs -fn mono:size=16"
```
