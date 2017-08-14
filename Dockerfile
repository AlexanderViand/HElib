FROM ubuntu:16.04

# Required for HElib installation
RUN apt-get update && apt-get install -y \
	build-essential \
	wget 	\
	git		\
	gcc		\
	g++  	\
	make 	\
	m4   	\
	lzip

# Download and install cmake (for custom HElib build system)
RUN wget https://cmake.org/files/v3.9/cmake-3.9.1.tar.gz && \
    tar -xvf cmake-3.9.1.tar.gz && \
    cd cmake-3.9.1 && \
    ./bootstrap && \
    make && \
    make install

# Download and install GMP (always threadsafe)
RUN wget ftp://ftp.gnu.org/gnu/gmp/gmp-6.1.2.tar.lz && \
	tar -xf gmp-6.1.2.tar.lz && \
	cd gmp-6.1.2 &&		\
	./configure &&		\
	make &&				\
	make install

# Download and install NTL (threadsafe)
RUN wget http://www.shoup.net/ntl/ntl-10.5.0.tar.gz && \
	tar -xf ntl-10.5.0.tar.gz && \
	cd ntl-10.5.0/src && \
	./configure NTL_GMP_LIP=on NTL_THREADS=on NTL_THREAD_BOOST=on NTL_EXCEPTIONS=on NTL_STD_CXX11=on && \
	make && \
	make install

# Download and install HElib (threadsafe, with debug info)
RUN git clone https://github.com/AlexanderViand/HElib.git HElib && \
	cd HElib/src && \
	git checkout working &&\
	cmake . -DCMAKE_BUILD_TYPE=Debug && \
    make install_fhe