FROM fpco/stack-build:lts-12.16

RUN stack --resolver=lts-12.16 install Agda-2.5.4.2

RUN git clone https://github.com/agda/agda-stdlib /root/agda-stdlib && \
    cd /root/agda-stdlib && \
    git checkout v0.16.1 && \
    mkdir /root/.agda && \
    echo "/root/agda-stdlib/standard-library.agda-lib" > /root/.agda/libraries

RUN apt-get update && \
    apt-get install -y emacs

VOLUME /root/artifact/
COPY agda/ /root/artifact/
WORKDIR /root/artifact/

COPY vendor/emacs.el /root/.emacs

RUN cd /root/artifact && \
    agda src/Regular.agda
