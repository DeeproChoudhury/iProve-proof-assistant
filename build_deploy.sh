#!/bin/bash
yarn install
yarn build
serve -c ../serve.json -s build