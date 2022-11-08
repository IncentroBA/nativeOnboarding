## NativeOnboarding

Set up A simple Native Onboarding section.

## Features

A configurable set of onboarding pages.

Show skip button? (`boolean`).

Complete action.

Skip action.

Set colors for text and background elements.

## Usage

Generate a simple onboarding by filling the object list group settings. At least 1 'page' is required to add. A page consists of the following:

- Title
- Background color
- Subtitle
- Image

! Keep the content of the text limited, as the contents of the onboarding is not vertical scrollable.

## Development and contribution

1. Install NPM package dependencies by using: `npm install`. If you use NPM v7.x.x, which can be checked by executing `npm -v`, execute: `npm install --legacy-peer-deps`.
1. Run `npm start` to watch for code changes. On every change:
   - the widget will be bundled;
   - the bundle will be included in a `dist` folder in the root directory of the project;
   - the bundle will be included in the `deployment` and `widgets` folder of the Mendix test project.

[specify contribution]
