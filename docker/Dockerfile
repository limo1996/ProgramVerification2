FROM ubuntu:17.10
MAINTAINER Vytautas Astrauskas "vastrauskas@gmail.com"

ENV DEBIAN_FRONTEND noninteractive

# Install prerequisites.
RUN apt-get update && \
    apt-get install -y \
        build-essential \
        curl \
        wget \
        software-properties-common \
        unzip \
        gdebi-core \
        locales \
        python-dev \
        python3-dev \
        && \
    apt-get clean

ADD texlive.profile /tmp/texlive.profile

# Install texlive-2017.
RUN cd /tmp/ && \
    wget -q http://mirror.ctan.org/systems/texlive/tlnet/install-tl-unx.tar.gz -O /tmp/texlive.tar.gz && \
    tar -xf /tmp/texlive.tar.gz && \
    cd install-tl-* && \
    ./install-tl --profile=/tmp/texlive.profile && \
    rm -rf /tmp/*
ENV PATH $PATH:/usr/local/texlive/2017/bin/x86_64-linux/

# Install additional tools.
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        git \
        python-pip \
        python-setuptools \
        gnuplot \
        inkscape \
        && \
    apt-get clean && \
    pip install --upgrade pip && \
    pip install https://bitbucket.org/vakaras/pygments-main/get/tip.zip#egg=pygments && \
	wget -c https://raw.githubusercontent.com/vakaras/inkscape-export-layers/1b9f3f274c1e011bcc4b439e8a3d89d5d925c7aa/exportlayers.py -O /usr/bin/exportlayers && \
	chmod 755 /usr/bin/exportlayers

# Install Z3 (post v4.5.0).
RUN apt-get update && \
    apt-get install -y git build-essential python && \
    cd /tmp && \
    git clone https://github.com/Z3Prover/z3.git && \
    cd /tmp/z3 && \
    git checkout 3865c453827506fc5c9d6c6c7c3d66d17030f158 && \
    ./configure && \
    cd build && \
    make && \
    make install && \
    apt-get clean && \
    rm -rf /tmp/z3
env Z3_EXE /usr/bin/z3

# Install Java.
RUN apt-get update && \
    apt-get install -y openjdk-8-jdk ca-certificates-java && \
    update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java && \
    apt-get clean && \
    rm -rf /tmp/*

# Install SBT.
RUN apt-get update && \
    apt-get install apt-transport-https && \
    echo "deb https://dl.bintray.com/sbt/debian /" >> /etc/apt/sources.list.d/sbt.list && \
    apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823 && \
    apt-get update && \
    apt-get install sbt && \
    apt-get clean

# Install sudo, shell, etc.
RUN apt-get update && \
    apt-get install -y sudo fish man-db mercurial && \
    apt-get clean

# Set up locale.
RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# Set up home.
ENV HOME /home/developer
RUN mkdir -p /home/developer && \
    chmod 777 /home/developer && \
    echo "developer:x:1000:1000:Developer,,,:/home/developer:/usr/bin/fish" >> /etc/passwd && \
    echo "developer:x:1000:" >> /etc/group

# Mark container.
ENV TEXLIVE_CONTAINER 1

# Set the working directory.
WORKDIR /data
